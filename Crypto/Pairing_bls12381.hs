{-|
Module      : Pairing_bls12381
Description : Pairing over the BLS12-381 elliptic curve
Copyright   : (c) Eric Schorn, 2020
License     : GPL-3
Maintainer  : eschorn@integritychain.com
Stability   : experimental

Implements the BLS12-381 pairing calculation per https://electriccoin.co/blog/new-snark-curve/.
This code has no dependencies and utilizes no language options.

This code is for strictly educational purposes: simplicity and clarity are the primary
goals, so the code may be incomplete, inefficient, incorrect and/or insecure. Specifically,
both the algorithms within the code and (the use of) Haskell's arbitrary-precision integers
are clearly not constant-time and thus introduce timing side channels. This code has not
undergone a security audit; use at your own risk.

Note that field element constructors are not exported. Points can either be constructed
directly via the `g1Point` or `g2Point` functions, or they can be constructed from the
`pointMul` function given a scalar and typically either the `g1Generator` or `g2Generator`
points. Points are then used in the `pairing` function which returns `Fq12` elements that
can be tested for equality or shown. The Fq12 `*` operator is also exported to support
more elaborate pairing computations (see example below).

Coordinates and Points are internally validated to be on-curve. As such, the `g1Point`,
`g1Generator`, `g2Point`, `g2Generator` and `pointMul` functions all return `Maybe Points`
which will need to be unwrapped prior to use in the `pairing` function.

__Example usage:__

Demonstrate the following equality (note the constants shifting positions):

@pairing((12+34)*56*g1, 78*g2) == pairing(78*g1, 12*56*g2) * pairing(78*g1, 34*56*g2)@

where g1 and g2 are group generators. Below is a @ghci@ interpreter session.

@\$ ghci Crypto\/Pairing_bls12381.hs
\
*Pairing_bls12381> p_12p34m56 = g1Generator >>= pointMul ((12 + 34) * 56)
*Pairing_bls12381> q_78 = g2Generator >>= pointMul 78
*Pairing_bls12381> leftSide = pairing \<$\> p_12p34m56 \<*\> q_78 >>= id
*Pairing_bls12381>
*Pairing_bls12381> p_78 = g1Generator >>= pointMul 78
*Pairing_bls12381> q_12m56 = g2Generator >>= pointMul (12 * 56)
*Pairing_bls12381> q_34m56 = g2Generator >>= pointMul (34 * 56)
*Pairing_bls12381> pair2 = pairing \<$>\ p_78 \<*\> q_12m56 >>= id
*Pairing_bls12381> pair3 = pairing \<$>\ p_78 \<*\> q_34m56 >>= id
*Pairing_bls12381> rightSide = (*) \<$>\ pair2 \<*\> pair3
*Pairing_bls12381>
*Pairing_bls12381> (==) \<$\> leftSide \<*\> rightSide
Just True@
-}

module Pairing_bls12381 (g1Point, g2Point, g1Generator, g2Generator,
                 pointMul, pairing, prime, order, smokeTest, Num( (*) ) ) where

import Data.Bits (shiftR)
import Data.List (unfoldr)
import Data.Maybe (isNothing)

-- Tower extension fields. See https://eprint.iacr.org/2009/556.pdf
newtype Fq1 = Fq1 {t0 :: Integer} deriving (Eq, Show)
data Fq2 = Fq2 {u1 :: Fq1, u0 :: Fq1} deriving (Eq, Show)
data Fq6 = Fq6 {v2 :: Fq2, v1 :: Fq2, v0 :: Fq2} deriving (Eq, Show)
data Fq12 = Fq12 {w1 :: Fq6, w0 :: Fq6} deriving (Eq, Show)


-- Fields will implement `Num` along with these two functions
class (Num a) => Field a where
  inv :: a -> a
  mul_nonres :: a -> a


-- | The field prime constant used in BLS12-381 is exported for reference.
prime = 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab


-- Fq1 is 'standard' single-element finite field
instance Num Fq1 where

  (+) (Fq1 a0) (Fq1 b0) = Fq1 ((a0 + b0) `mod` prime)  -- Obvious perf enhancement here..

  (-) (Fq1 a0) (Fq1 b0) = Fq1 ((a0 - b0) `mod` prime)  -- ..and here; stick with simplicity

  (*) (Fq1 a0) (Fq1 b0) = Fq1 ((a0 * b0) `mod` prime)

  fromInteger a0 = Fq1 (a0 `mod` prime)

  abs = error "not needed/implemented for Fq1"

  signum = error "not needed/implemented for Fq1"


instance Field Fq1 where

  mul_nonres a0 = a0

  inv (Fq1 a0) = if a0 == 0 then error "inverse of 0" else Fq1 (beea a0 prime 1 0 prime)


-- Fq2 is constructed with Fq1(u) / (u^2 - β) where β = -1.
instance Num Fq2 where

  (+) (Fq2 a1 a0) (Fq2 b1 b0) = Fq2 (a1 + b1) (a0 + b0)

  (-) (Fq2 a1 a0) (Fq2 b1 b0) = Fq2 (a1 - b1) (a0 - b0)

  (*) (Fq2 a1 a0) (Fq2 b1 b0) = Fq2 (a1 * b0 + a0 * b1) (a0 * b0 - a1 * b1)

  fromInteger a0 = Fq2 0 (fromInteger a0)

  abs = error "not needed/implemented for Fq2"

  signum = error "not needed/implemented for Fq2"


instance Field Fq2 where

  mul_nonres (Fq2 a1 a0) = Fq2 (a1 + a0) (a0 - a1)

  inv (Fq2 a1 a0) = Fq2 (-a1 * factor) (a0 * factor)
    where
      factor = inv (a1 * a1 + a0 * a0)


-- Fq6 is constructed with Fq2(v) / (v^3 - ξ) where ξ = u + 1
instance Num Fq6 where

  (+) (Fq6 a2 a1 a0) (Fq6 b2 b1 b0) = Fq6 (a2 + b2) (a1 + b1) (a0 + b0)

  (-) (Fq6 a2 a1 a0) (Fq6 b2 b1 b0) = Fq6 (a2 - b2) (a1 - b1) (a0 - b0)

  (*) (Fq6 a2 a1 a0) (Fq6 b2 b1 b0) = Fq6 t2 (t1 + t4) (t0 + t3)
    where
      t0 = a0 * b0
      t1 = a0 * b1 + a1 * b0
      t2 = a0 * b2 + a1 * b1 + a2 * b0
      t3 = mul_nonres (a1 * b2 + a2 * b1)
      t4 = mul_nonres (a2 * b2)

  fromInteger a0 = Fq6 0 0 (fromInteger a0)

  abs = error "not needed/implemented for Fq6"

  signum = error "not needed/implemented for Fq6"


instance Field Fq6 where

  mul_nonres (Fq6 a2 a1 a0) = Fq6 a1 a0 (mul_nonres a2)

  inv (Fq6 a2 a1 a0) = Fq6 (t2 * factor) (t1 * factor) (t0 * factor)
    where
      t0 = a0 * a0 - mul_nonres (a1 * a2)
      t1 = mul_nonres (a2 * a2) - a0 * a1
      t2 = a1 * a1 - a0 * a2
      factor = inv (a0 * t0 + mul_nonres (a2 * t1) + mul_nonres (a1 * t2))



-- Fq12 is constructed with Fq6(w) / (w^2 - γ) where γ = v
instance Num Fq12 where

  (+) (Fq12 a1 a0) (Fq12 b1 b0) = Fq12 (a1 + b1) (a0 + b0)

  (-) (Fq12 a1 a0) (Fq12 b1 b0) = Fq12 (a1 - b1) (a0 - b0)

  (*) (Fq12 a1 a0) (Fq12 b1 b0) = Fq12 (a1 * b0 + a0 * b1) (a0 * b0 + mul_nonres (a1 * b1))

  fromInteger a0 = Fq12 0 (fromInteger a0)

  abs = error "not needed/implemented for Fq12"

  signum = error "not needed/implemented for Fq12"


instance Field Fq12 where

  mul_nonres _ = error "not needed for Fq12"

  inv (Fq12 a1 a0) = Fq12 (-a1 * factor) (a0 * factor)
    where
      factor = inv (a0 * a0 - mul_nonres (a1 * a1))



-- Binary Extended Euclidean Algorithm (note that there are no divisions)
-- See: Guide to Elliptic Curve Cryptography by Hankerson, Menezes, and Vanstone
beea :: Integer -> Integer -> Integer -> Integer -> Integer -> Integer
beea u v x1 x2 p
  | not (u > 0 && v > 0) = error "beea operands u,v must be greater than zero"
  | u == 1 = mod x1 p
  | v == 1 = mod x2 p
  | even u = if even x1 then beea (shiftR u 1) v (shiftR x1 1) x2 p
                        else beea (shiftR u 1) v (shiftR (x1 + p) 1) x2 p
  | even v = if even x2 then beea u (shiftR v 1) x1 (shiftR x2 1) p
                        else beea u (shiftR v 1) x1 (shiftR (x2 + p) 1) p
  | u >= v = beea (u - v) v (x1 - x2) x2 p
  | u < v  = beea u (v - u) x1 (x2 - x1) p


-- Note we use Affine coordinates throughout for simplicity. However, projective
-- coordinates could easily be inserted here...
data Point a = Affine {ax :: a, ay :: a}
             | PointAtInfinity deriving (Eq, Show)


-- | The curve order constant of BLS12-381 is exported for reference.
order = 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001


-- | The standard generator point for G1.
g1Generator = Just (Affine (Fq1 0x17f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb)
                     (Fq1 0x08b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e1))


-- | The standard generator point for G2.
g2Generator = Just (Affine (Fq2 (Fq1 0x13e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e)
                          (Fq1 0x024aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb8))
                     (Fq2 (Fq1 0x0606c4a02ea734cc32acd2b02bc28b99cb3e287e85a763af267492ab572e99ab3f370d275cec1da1aaa9075ff05f79be)
                          (Fq1 0x0ce5d527727d6e118cc9cdc6da2e351aadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b82801)))


-- BLS12-381 curve(s) are E1: y^2 = x^3 + 4 and E2: y^2 = x^3 + 4(i+1)
isOnCurve :: (Field a, Eq a) => Point a -> Bool
isOnCurve PointAtInfinity = False
isOnCurve a0 = ay a0^2 == (ax a0^3 + mul_nonres 4)  -- mul_nonres fixes constant for E2


-- | Given @x@ and @y@, construct a valid point contained in G1.
g1Point :: Integer -> Integer -> Maybe (Point Fq1)
g1Point x y = if isOnCurve candidate then Just candidate else Nothing
  where
    candidate = Affine (Fq1 (x `mod` prime)) (Fq1 (y `mod` prime))


-- | Given @xi@, @x@, @yi@ and @y@, construct a valid point contained in G2.
g2Point :: Integer -> Integer -> Integer -> Integer -> Maybe (Point Fq2)
g2Point x1 x0 y1 y0 = if isOnCurve candidate then Just candidate else Nothing
  where
    candidate = Affine (Fq2 (Fq1 (x1 `mod` prime)) (Fq1 (x0 `mod` prime)))
                       (Fq2 (Fq1 (y1 `mod` prime)) (Fq1 (y0 `mod` prime)))


-- Add affine curve points; handle all corner cases
pointAdd :: (Field a, Eq a) => Point a -> Point a -> Point a
pointAdd PointAtInfinity q = q
pointAdd p PointAtInfinity = p
pointAdd p q
  | p == q = pointDouble p
pointAdd Affine {ax=x1, ay=y1} Affine {ax=x2, ay=y2}
  | x1 == x2 && y1 /= y2 = PointAtInfinity
pointAdd Affine {ax=x1, ay=y1} Affine {ax=x2, ay=y2} = Affine {ax=x3, ay=y3}
  where
    slope = (y2 - y1) * inv (x2 - x1)
    x3 = slope * slope - x1 - x2
    y3 = slope * (x1 - x3) - y1


-- Double affine curve points
pointDouble :: (Field a) => Point a -> Point a
pointDouble PointAtInfinity = PointAtInfinity
pointDouble Affine {ax=x1, ay=y1} = Affine {ax=x3, ay=y3}
  where
    x1_squared = x1 * x1
    slope = (3 * x1_squared) * inv (2 * y1)
    x3 = slope * slope - x1 - x1
    y3 = slope * (x1 - x3) - y1


-- | Multiply a positive integer and valid point in either G1 or G2.
pointMul :: (Field a, Eq a) => Integer -> Point a -> Maybe (Point a)
pointMul scalar base
  | isOnCurve base && scalar > 0 = Just (pointMul' scalar base PointAtInfinity)
  | otherwise = Nothing


-- Double and add helper loop
pointMul' :: (Field a, Eq a) => Integer -> Point a -> Point a -> Point a
pointMul' scalar base accum
  | scalar == 0 = accum
  | odd scalar  = pointMul' (shiftR scalar 1) doubleBase (pointAdd accum base)
  | even scalar = pointMul' (shiftR scalar 1) doubleBase accum
  where
    doubleBase = pointAdd base base


-- Untwist point on E2 for pairing calculation
untwist :: Point Fq2 -> Point Fq12
untwist Affine {ax=x1, ay=y1} = Affine {ax=wide_x, ay=wide_y}
  where
    root = Fq6 0 1 0
    wsq = inv (Fq12 0 root)
    wcu = inv (Fq12 root 0)
    wide_x = Fq12 0 (Fq6 0 0 x1) * wsq
    wide_y = Fq12 0 (Fq6 0 0 y1) * wcu


doubleEval :: Point Fq2 -> Point Fq1 -> Fq12
doubleEval r p = fromInteger (t0 (ay p)) - (fromInteger (t0 (ax p)) * slope) - v
  where
    r_new = untwist r
    rx2 = ax r_new * ax r_new
    slope = (3 * rx2) * inv (2 * ay r_new)
    v = ay r_new - slope * ax r_new


-- Used in miller loop when current bit index is true
addEval :: Point Fq2 -> Point Fq2 -> Point Fq1 -> Fq12
addEval r q p = if (ax new_r == ax new_q) && (ay new_r == - ay new_q)
                    then fromInteger (t0 (ax p)) - ax new_r
                    else addEval' new_r new_q p
  where
    new_r = untwist r
    new_q = untwist q


addEval' :: Point Fq12 -> Point Fq12 -> Point Fq1 -> Fq12
addEval' new_r new_q p = fromInteger (t0 (ay p)) - (fromInteger (t0 (ax p)) * slope) - v
  where
    slope = (ay new_q - ay new_r) * inv (ax new_q - ax new_r)
    v = ((ay new_q * ax new_r) - (ay new_r * ax new_q)) * inv (ax new_r - ax new_q)


-- Classic Miller loop for Ate pairing
miller :: Point Fq1 -> Point Fq2 -> Fq12
miller p q = miller' p q q iterations 1
  where
    iterations = tail $ reverse $
      unfoldr (\b -> if b == (0 :: Integer) then Nothing
                                            else Just(odd b, shiftR b 1)) 0xd201000000010000


-- Double and add helper for miller
miller' :: Point Fq1 -> Point Fq2 -> Point Fq2 -> [Bool] -> Fq12 -> Fq12
miller' p q r [] result = result
miller' p q r (i:iters) result = if i then miller' p q (pointAdd doubleR q) iters (accum * addEval doubleR q p)
                                      else miller' p q doubleR iters accum
  where
    accum = result^2 * doubleEval r p
    doubleR = pointDouble r


-- Used for the final exponentiation; opportunity for further performance optimization
pow' :: (Field a) => a -> Integer -> a -> a
pow' a0 exp result
  | exp <= 1 = a0
  | even exp = accum * accum
  | otherwise = accum * accum * a0
  where accum = pow' a0 (shiftR exp 1) result


-- | Pairing calculation for a point in G1 and another point in G2.
pairing :: Point Fq1 -> Point Fq2 -> Maybe Fq12
pairing p_g1 q_g2
  | isOnCurve p_g1 && isOnCurve q_g2 = Just (pow' (miller p_g1 q_g2) (div (prime^12 - 1) order) 1)
  | otherwise = Nothing



-- | A quick test of internal field arithmetic, curve operations and pairing; returns success.
smokeTest :: Bool
smokeTest = True -- and $ res1 ++ res2 ++ res6 ++ res12 ++ resGs ++ resO ++ resPr
--  where
--    operands  = [100..1100]
--    res1  = [(fromInteger x :: Fq1)  * inv (fromInteger x) == 1 | x <- operands]
--    res2  = [(fromInteger x :: Fq2)  * inv (fromInteger x) == 1 | x <- operands]
--    res6  = [(fromInteger x :: Fq6)  * inv (fromInteger x) == 1 | x <- operands]
--    res12 = [(fromInteger x :: Fq12) * inv (fromInteger x) == 1 | x <- operands]
--    resGs = [
--      (g1Generator >>= (pointMul 0x49abcbaa08d87d1cba8fd9c0ea04df30b94df934827a7383098ac39e1aafc218)) == Just Affine
--        {ax = Fq1 0x019906b4953328ec688ffc9e41ea7d79d295c7de6249eb0397680306c5fe3aa3bbb45324bdbc379e8e4116166f2a0d40,
--         ay = Fq1 0x165f11693959e7193af31b99b724f95d7b49baa2394b758c2455ef725f32abd56361e1e151f2bbd7a7efc6f3bb5652d4},
--      (g2Generator >>= (pointMul 0x49abcbaa08d87d1cba8fd9c0ea04df30b94df934827a7383098ac39e1aafc218))  == Just Affine
--        {ax = Fq2 (Fq1 0x02433912fa403e0d19d39c7687eb1041f474a82fdd646b1a35afb4d088f11469467468f1ba16c3e5838503919bdbfa24)
--                  (Fq1 0x14906db96db027e17449a1323198cfccde4d15456ce09f3fef4c7baed5495463b7cc750300e0e2918d5680d97a567122),
--         ay = Fq2 (Fq1 0x0e82e52250625e4c0864645fba3b36e24c36dbc3d4bae0ca40b0c28b0e3780bf6b8d022c032727e8195e2a2b547be84b)
--                  (Fq1 0x0f240b0ffee3ac62cd5576f012a92cd78c9ded14c11c7637caff4daf885c9a258783a7aef4dc1815737a5b606e03868e)}
--      ]
--    resO = [(g1Generator >>= (pointMul order)) == Just PointAtInfinity,
--            (g2Generator >>= (pointMul order)) == Just PointAtInfinity]


--    scalar_1 = [100..102]
--    scalar_2 = [200..202]
--    p_g1 = [g1Generator >>= (pointMul x) | x <- scalar_1]
--    p_g2 = [g2Generator >>= (pointMul x) | x <- scalar_1]
--    q_g1 = [g1Generator >>= (pointMul x) | x <- scalar_2]
--    q_g2 = [g2Generator >>= (pointMul x) | x <- scalar_2]
--    pairing1 = [pairing p q | (Just p) <- p_g1, (Just q) <- q_g2]
--    pairing2 = [pairing q p | (Just p) <- p_g2, (Just q) <- q_g1]
--    resPr = [
--      pairing1 == pairing2,
--      (==) <$> pairing1 <*> pairing2,
--      Nothing `notElem` (p_g1 ++ q_g1),
--      Nothing `notElem` (p_g2 ++ q_g2),
--      Nothing `notElem` (pairing1 ++ pairing2),
--      isNothing (g1Point 1 2),
--      isNothing (g2Point 1 2 3 4),
--      all (\(Just p) -> pow' p order 0 == 1) pairing2
--      ]



-- TODO: Test each internal function only --> Fqx, pow <only stuff that cannot be tested from outside>
