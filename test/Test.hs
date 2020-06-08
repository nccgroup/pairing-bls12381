module Main where

import Test.Tasty
import qualified Test.Tasty.HUnit as HU
import Pairing_bls12381


main :: IO ()
main = defaultMain $ testGroup "\nRunning Tests" [huTst_SmokeTest, huTst_Pairing, huTst_Points]


huTst_SmokeTest :: TestTree
huTst_SmokeTest = HU.testCase "huTst_smokeTest" $ HU.assertBool "mismatch" smokeTest


huTst_Pairing :: TestTree
huTst_Pairing = HU.testCase "huTst_Pairing" $
  do
    let scalar_1 = [100..102]
    let scalar_2 = [200..202]
    let p_g1 = [g1Generator >>= (pointMul x) | x <- scalar_1]
    let p_g2 = [g2Generator >>= (pointMul x) | x <- scalar_1]
    let q_g1 = [g1Generator >>= (pointMul x) | x <- scalar_2]
    let q_g2 = [g2Generator >>= (pointMul x) | x <- scalar_2]
    let pairing1 = [pairing <$> p <*> q | p <- p_g1, q <- q_g2]
    let pairing2 = [pairing <$> q <*> p | p <- p_g2, q <- q_g1]
    HU.assertBool "mismatch 3" (all (\(p1, p2) -> p1 == p2) (zip pairing1 pairing2))

huTst_Points :: TestTree
huTst_Points = HU.testCase "huTst_Points" $
  do
    let (Just p1) = g1Point 0x14ade5f375a7e7194bf5244ace032817f63ff854f22654e3c0855511156fe98ba5c092ad9d68011f783e0f418619b2f2
                               0x0b54adeba0fdaeeaec7a7146c738c7ebf3f44158475541427ce976fe020e52dedd97feba12c7272b8f3dc49a7d122f8d
    let (Just q1) = g2Point 0x14ebc73c50a68b2333c169565ab75e35c03caaae6573884db2557a6731eca4c643bf7156cb6a2fee60b079577d4732e6
                               0x64974dc7ff588a0b38e37da6b767b91d068924526dd8698f131b6f19b309065aab861b33411675781d9d42b63935c85
                               0x16048641e0249a5ff6cb1b4a8c9194589148c1903b800752d8a6c09867508952d14fecb015cc4f337372b29bc32b08b1
                               0x172f08bfdf8fca06c461c9978e8d8f7de5126a9ee74d086a82d90545d9180e3f9199a7fd2fbd022a9bcfa833ec321e0a
    let (Just res1) = pairing p1 q1
    let (Just p2) = g1Point 0x19097e1378ae74067593c7e6b71fc8ec41d11e8e1b67b9ca47475e2eb02d5959cfb4bb09a3cb4c7fc14506629b4176d1
                        0xe41648923fc4a39b9e0e0f3d4b0fdcae45caad07622e2d40e67d2eea13bff92f071c0cf4b6687417efdadfae4fec00a
    let (Just q2) = g2Point 0xda18340291cbdd3cfaf596d62fe88f4cf211e8a2439f736786c12fba4e66cccb9279ef1a814d81785bec778c60f9284
                        0xa1d6930cfb119d6b2c52f8260217bf7859437e6aa8b8ca891ce74886f7c667274507b6f107a0c4c7618fe2f3571fcb2
                        0x9745aac53daa7296110ad436829ec3cfd8fbc83012878608479a11caf2ada57c95dd64fd5fd3d4cf3cdf536defd288
                        0x1831856291ad777b5e8f2eff3c2a4efe23a56f44ad97cda5c77f5a9c51bef1e13691011ab1979568363f5b1fecdd32d6
    let (Just res2) = pairing p2 q2
    HU.assertBool "mismatch" (res1 == res2)





-- TODO
  -- Test each and every exported function