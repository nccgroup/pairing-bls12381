module Sqrt where

import Data.Bits (shiftR)
import Data.Maybe (fromJust)
-- import Debug.Trace (trace)

powMod :: Integer -> Integer -> Integer -> Integer
powMod a exp q | exp < 0 || q < 1 = error "Invalid exponent or modulus"
powMod a 0 q = 1
powMod a 1 q = a
powMod a exp q | even exp = powMod (a * a `mod` q) (shiftR exp 1) q
               | otherwise = a * powMod a (exp - 1) q `mod` q


bls12381Prime :: Integer  -- Congruent to 3 mod 4
bls12381Prime = 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab

sqrt_3mod4 :: Integer -> Integer -> Maybe Integer
sqrt_3mod4 _ q | q < 3 || (q `mod` 4) /= 3 = error "Invalid modulus"
sqrt_3mod4 a q = result
  where
    t1 = powMod a ((q + 1) `div` 4) q
    result = if powMod t1 2 q == a then Just t1 else Nothing


curve25519Prime :: Integer
curve25519Prime = 2^255 - 19

sqrt_5mod8 :: Integer -> Integer -> Maybe Integer
sqrt_5mod8 _ q | q < 3 || (q `mod` 8) /= 5 = error "Invalid modulus"
sqrt_5mod8 a q = result
  where
    c1 = fromJust $ sqrt_ts (q - 1) q  -- Can be precomputed with fixed modulus
    c2 = (q + 3) `mod` 8               -- Can be precomputed with fixed modulus
    t1 = powMod a c2 q
    t2 = (t1 * c1) `mod` q
    result = if powMod t1 2 q == a then Just t1            -- Not constant-time
               else if powMod t2 2 q == a then Just t2     -- Not constant-time
                 else Nothing  -- Perhaps `a` was not square, modulus not prime

p9mod16Prime :: Integer
p9mod16Prime = 0x40000000000000000000000000000000224698fc094cf91b992d30ed00000e99

sqrt_9mod16 :: Integer -> Integer -> Maybe Integer
sqrt_9mod16 _ q | q < 3 || (q `mod` 16) /= 9 = error "Invalid modulus"
sqrt_9mod16 a q = result
  where
    c1 = fromJust $ sqrt_ts (q - 1) q  -- Can be precomputed with fixed modulus
    c4 = fromJust $ sqrt_ts c1 q       -- Can be precomputed with fixed modulus
    c2 = (q + 7) `div` 16
    t1 = powMod a c2 q
    t2 = (t1 * c1) `mod` q
    t3 = (t1 * c4) `mod` q
    t4 = (t2 * c4) `mod` q
    result = if powMod t1 2 q == a then Just t1            -- Not constant-time
               else if powMod t2 2 q == a then Just t2     -- Not constant-time
                 else if powMod t3 2 q == a then Just t3   -- Not constant-time
                   else if powMod t4 2 q == a then Just t4 -- Not constant-time
                     else Nothing  -- Perhaps `a` was not square, modulus not prime


write_qm1_eq_2sr :: Integer -> (Integer, Integer)
write_qm1_eq_2sr q | q < 3 = error "Invalid modulus"
write_qm1_eq_2sr q = (s, r)
  where
    s = count (q - 1)
      where
        count qq | odd qq || qq == 0 = 0
                 | even qq = 1 + count(shiftR qq 1)
    r = (q - 1) `div` (2^s)


eulerCriterion :: Integer -> Integer -> Integer
eulerCriterion a q | even q || q < 3 = error "Invalid arguments"
eulerCriterion a q = powMod a ((q - 1) `div` 2) q


sqrt_ts :: Integer -> Integer -> Maybe Integer
sqrt_ts a q = if powMod result 2 q == a then Just result else Nothing
  where
    (c1, c2) = write_qm1_eq_2sr q
    c3 = (c2 - 1) `div` 2
    c4 = head (filter (\x -> (q-1) == eulerCriterion x q) [1..])
    c5 = powMod c4 c2 q
    z1 = powMod a c3 q
    t1 = z1 * z1
    t = t1 * a
    z = z1 * a
    b = t
    c = c5
    result = for_i c1 b z c t
      where
        for_i 1   _ z _ _ = z
        for_i xc1 b z c t = for_i (xc1 - 1) b_new z_new c_new t_new
          where
            b_pow = if xc1 == 2 then b else powMod b (2 ^ (xc1 - 2)) q
            e = (b_pow == 1)
            zt = (z * c) `mod` q
            z_new = if e then z else zt
            c_new = (c * c) `mod` q
            tt = (t * c_new) `mod` q
            t_new = if e then t else tt
            b_new = t_new




testMe = (squares == actual)
  where
    squares = [x * x `mod` p9mod16Prime | x <- [10..1000]]
    roots = map (\x -> fromJust $ sqrt_9mod16 x p9mod16Prime) squares
    actual = map (\x -> x * x `mod` p9mod16Prime) roots
