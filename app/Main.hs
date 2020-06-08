module Main ( main )where

import Prelude (IO, print)
import Pairing_bls12381 (g1Generator)

main :: IO ()
main = print retval
  where
    retval = g1Generator
    --print retval
