module Sqrt where

import Data.Bits (shiftR)
import Data.Maybe (fromJust)
import Debug.Trace (trace)
import System.Random (RandomGen, mkStdGen, randomR)
import Control.Exception

-- Result = a^exp mod q
powMod :: Integer -> Integer -> Integer -> Integer
powMod a exp q | exp < 0 || q < 1 = error "Invalid exponent or modulus"
powMod a 0 q = 1
powMod a 1 q = a
powMod a exp q | even exp  = powMod (a * a `mod` q) (shiftR exp 1) q
               | otherwise = a * powMod a (exp - 1) q `mod` q


bls12381Prime :: Integer  -- Prime q congruent to 3 mod 4
bls12381Prime = 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab

-- Result = Maybe square_root(a) mod q when q is congruent to 3 mod 4
sqrt_3mod4 :: Integer -> Integer -> Maybe Integer
sqrt_3mod4 _ q | q < 3 || (q `mod` 4) /= 3 = error "Invalid modulus"
sqrt_3mod4 a q = result
  where
    cq = (q + 1) `div` 4
    r1 = powMod a cq q
    result = if powMod r1 2 q == a then Just r1 else Nothing


curve25519Prime :: Integer  -- Prime q congruent to 5 mod 8
curve25519Prime = 2^255 - 19

-- Result = Maybe square_root(a) mod q when q is congruent to 5 mod 8
sqrt_5mod8 :: Integer -> Integer -> Maybe Integer
sqrt_5mod8 _ q | q < 3 || (q `mod` 8) /= 5 = error "Invalid modulus"
sqrt_5mod8 a q = result
  where
    cq = (q + 3) `div` 8
    c2 = fromJust $ sqrt_ts (q - 1) q  -- square_root(-1)
    r1 = powMod a cq q
    r2 = (r1 * c2) `mod` q             -- r * square_root(-1)
    result = if powMod r1 2 q == a then Just r1
               else if powMod r2 2 q == a then Just r2
                 else Nothing  -- Perhaps `a` not square, modulus not prime


p9mod16Prime :: Integer  -- Prime q congruent to 9 mod 16
p9mod16Prime = 0x40000000000000000000000000000000224698fc094cf91b992d30ed00000e99

-- Result = Maybe square_root(a) mod q when q is congruent to 9 mod 16
sqrt_9mod16 :: Integer -> Integer -> Maybe Integer
sqrt_9mod16 _ q | q < 3 || (q `mod` 16) /= 9 = error "Invalid modulus"
sqrt_9mod16 a q = result
  where
    cq = (q + 7) `div` 16
    c2 = fromJust $ sqrt_ts (q - 1) q -- square_root(-1)
    c4 = fromJust $ sqrt_ts c2 q      -- fourth_root(-1)
    r1 = powMod a cq q
    r2 = (r1 * c2) `mod` q            -- r * square_root(-1)
    r3 = (r1 * c4) `mod` q            -- r * fourth_root(-1)
    r4 = (r2 * c4) `mod` q            -- r * square_root(-1) * fourth_root(-1)
    result = if powMod r1 2 q == a then Just r1
               else if powMod r2 2 q == a then Just r2
                 else if powMod r3 2 q == a then Just r3
                   else if powMod r4 2 q == a then Just r4
                     else Nothing  -- Perhaps `a` not square, modulus not prime


-- Write q - 1 = p * 2^s; result = (p, s)
write_qm1_eq_p2s :: Integer -> (Integer, Integer)
write_qm1_eq_p2s q | q < 3 = error "Invalid modulus"
write_qm1_eq_p2s q = (p, s)
  where
    s = snd $ until (odd . fst) (\(q, i) -> (shiftR q 1, i + 1)) (q - 1, 0)
    p = (q - 1) `div` (2^s)


-- Result = 1 if a is quadratic residue mod q; otherwise result = q - 1
eulerCriterion :: Integer -> Integer -> Integer
eulerCriterion a q | even q || q < 3 = error "Invalid arguments"
eulerCriterion a q = powMod a ((q - 1) `div` 2) q


pallasPrime :: Integer  -- Prime q = p*2^s + 1, where p is large and s=32
pallasPrime = 0x40000000000000000000000000000000224698fc094cf91b992d30ed00000001

-- Result = Maybe square_root(a) mod q for arbitrary prime q
sqrt_var :: Integer -> Integer -> Maybe Integer
sqrt_var n p = if powMod result 2 p == n then Just result else Nothing
  where
    (q, s) = write_qm1_eq_p2s p
    z = head [x | x <- [1..], p - 1 == eulerCriterion x p]
    c =  powMod z q p
    t =  powMod n q p
    r =  powMod n ((q + 1) `div` 2) p
    result = loopy t r c s
      where
        loopy 0 _ _ _ = 0
        loopy 1 r _ _ = r
        loopy t r c s = assert invariants (loopy t_new r_new c_new s_new)  -- asserts only in ghci
          where
            i = head [i | i <- [1..s], powMod t (2^i) p == 1]
            b = powMod c (2^(s-i-1)) p
            s_new = i
            c_new =  powMod b 2 p
            t_new = (t * (powMod b 2 p)) `mod` p
            r_new = r * b `mod` p
            invariants = (s_new < s) &&
                         (powMod t_new (2^(s_new - 1)) p) == 1 &&
                         (powMod r_new 2 p) == (t_new * n `mod` p) &&
                         (powMod c_new (2^(s_new - 1)) p) == (p - 1)


sqrt_ts :: Integer -> Integer -> Maybe Integer
sqrt_ts a q = if powMod result 2 q == a then Just result else Nothing
  where
    (c2, c1) = write_qm1_eq_p2s q
    c3 = (c2 - 1) `div` 2
    c4 = head (filter (\x -> (q - 1) == eulerCriterion x q) [1..])
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
            b_pow = powMod b (2 ^ (xc1 - 2)) q -- if xc1 == 0 then b else powMod b (2 ^ (xc1 - 2)) q
            e = (b_pow == 1)
            zt = (z * c) `mod` q
            z_new = if e then z else zt
            c_new = (c * c) `mod` q
            tt = (t * c_new) `mod` q
            t_new = if e then t else tt
            b_new = t_new





testSqrt :: RandomGen b => (Integer -> Integer -> Maybe Integer) -> Integer -> Integer -> b -> (Bool, b)
testSqrt func prime     0 rndGen = (True, rndGen)
testSqrt func prime count rndGen = result
  where
    (rndRoot, rndGenNext) = randomR (2, prime - 1) rndGen
    xx = func (rndRoot^2 `mod` prime) prime
    res = if xx /= Nothing then fromJust xx else error ("Bad root: " ++ show rndRoot)
    -- res = fromJust $ func (rndRoot^2 `mod` prime) prime
    good = (res^2 `mod` prime == rndRoot^2 `mod` prime)
    result = if not good then (False, rndGenNext) else testSqrt func prime (count-1) rndGenNext


testGo_ts0 = testSqrt sqrt_ts pallasPrime  1000 (mkStdGen 100)
testGo_ts1 = testSqrt sqrt_ts bls12381Prime  1000 (mkStdGen 200)
testGo_ts2 = testSqrt sqrt_ts curve25519Prime  1000 (mkStdGen 300)  -- TODO: Fail?!?!
testGo_ts3 = testSqrt sqrt_ts p9mod16Prime  1000 (mkStdGen 400)  -- TODO: Fail?!?!

testGo_var0 = testSqrt sqrt_var pallasPrime     1000 (mkStdGen 100)  --10M -> 30min
testGo_var1 = testSqrt sqrt_var bls12381Prime   1000 (mkStdGen 200)
testGo_var2 = testSqrt sqrt_var curve25519Prime 1000 (mkStdGen 300)
testGo_var3 = testSqrt sqrt_var p9mod16Prime    1000 (mkStdGen 400)

testGo_3mod4 = testSqrt sqrt_3mod4 bls12381Prime   1000 (mkStdGen 100)
testGo_5mod8 = testSqrt sqrt_5mod8 curve25519Prime 1000 (mkStdGen 200)
testGo_9mod16 = testSqrt sqrt_9mod16 p9mod16Prime  1000 (mkStdGen 300)
