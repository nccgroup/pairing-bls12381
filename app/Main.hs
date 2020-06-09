module Main where


import Data.Maybe(fromJust)
import Control.Monad (join)
import Pairing_bls12381


main :: IO ()
main =
  do
    let scalar_1 = [100..109]  -- 10X5 = 50 * 2 = 100 pairings; 10*2 + 5*2 = 30 pointMuls
    let scalar_2 = [200..204]
    let p_g1 = [g1Generator >>= pointMul x | x <- scalar_1]
    let p_g2 = [g2Generator >>= pointMul x | x <- scalar_1]
    let q_g1 = [g1Generator >>= pointMul x | x <- scalar_2]
    let q_g2 = [g2Generator >>= pointMul x | x <- scalar_2]
    let pairing1 = [Control.Monad.join (pairing <$> p <*> q) | p <- p_g1, q <- q_g2]
    let pairing2 = [Control.Monad.join (pairing <$> q <*> p) | p <- p_g2, q <- q_g1]
    let result = all (\(p1, p2) -> fromJust p1 == fromJust p2) (zip pairing1 pairing2)
    print result
