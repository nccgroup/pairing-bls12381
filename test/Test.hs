module Main where


import Control.Monad (join)
import Test.Tasty
import qualified Test.Tasty.HUnit as HU
import Pairing_bls12381


main :: IO ()
main = defaultMain $ testGroup "\nRunning Tests" [huTstSmokeTest, huTstCurve,
  huTstPairingPts, huTstPointNeg, huTstPairingMul, huTstPairingAgg, huTstPairingGen]


huTstSmokeTest :: TestTree
huTstSmokeTest = HU.testCase "huTstSmokeTest" $ HU.assertBool "bad SmokeTest" smokeTest


huTstCurve :: TestTree
huTstCurve = HU.testCase "huTstCurve" $
  do
    HU.assertBool "bad g1 pointMul"
      ((g1Generator >>= pointMul 0x49abcbaa08d87d1cba8fd9c0ea04df30b94df934827a7383098ac39e1aafc218) ==
        g1Point 0x019906b4953328ec688ffc9e41ea7d79d295c7de6249eb0397680306c5fe3aa3bbb45324bdbc379e8e4116166f2a0d40
                0x165f11693959e7193af31b99b724f95d7b49baa2394b758c2455ef725f32abd56361e1e151f2bbd7a7efc6f3bb5652d4)
    HU.assertBool "bad g2 pointMul"
      ((g2Generator >>= pointMul 0x49abcbaa08d87d1cba8fd9c0ea04df30b94df934827a7383098ac39e1aafc218) ==
        g2Point 0x02433912fa403e0d19d39c7687eb1041f474a82fdd646b1a35afb4d088f11469467468f1ba16c3e5838503919bdbfa24
                0x14906db96db027e17449a1323198cfccde4d15456ce09f3fef4c7baed5495463b7cc750300e0e2918d5680d97a567122
                0x0e82e52250625e4c0864645fba3b36e24c36dbc3d4bae0ca40b0c28b0e3780bf6b8d022c032727e8195e2a2b547be84b
                0x0f240b0ffee3ac62cd5576f012a92cd78c9ded14c11c7637caff4daf885c9a258783a7aef4dc1815737a5b606e03868e)


huTstPointNeg :: TestTree
huTstPointNeg = HU.testCase "huTstPointNeg" $
  do
    let g1p31 = g1Generator >>= pointMul 31
    let g1p10 = g1Generator >>= pointMul 10
    let g1n21 = g1Generator >>= pointMul (-21)
    let sum10 = pointAdd <$> g1p31 <*> g1n21
    HU.assertBool "bad pointNeg 1" (sum10 == g1p10)
    let g1n30 = g1Generator >>= pointMul (-30)
    let s1um1 = pointAdd <$> g1p31 <*> g1n30
    HU.assertBool "bad pointNeg 2" (g1Generator == s1um1)
    let g2p31 = g2Generator >>= pointMul 31
    let g2p10 = g2Generator >>= pointMul 10
    let g2n21 = g2Generator >>= pointMul (-21)
    let s2um10 = pointAdd <$> g2p31 <*> g2n21
    HU.assertBool "bad pointNeg 3" (s2um10 == g2p10)
    let g2n30 = g2Generator >>= pointMul (-30)
    let s2um1 = pointAdd <$> g2p31 <*> g2n30
    HU.assertBool "bad pointNeg 4" (g2Generator == s2um1)


huTstPairingPts :: TestTree
huTstPairingPts = HU.testCase "huTstPairingPts" $
  do
    let p1 = g1Point 0x14ade5f375a7e7194bf5244ace032817f63ff854f22654e3c0855511156fe98ba5c092ad9d68011f783e0f418619b2f2
                     0x0b54adeba0fdaeeaec7a7146c738c7ebf3f44158475541427ce976fe020e52dedd97feba12c7272b8f3dc49a7d122f8d
    let q1 = g2Point 0x14ebc73c50a68b2333c169565ab75e35c03caaae6573884db2557a6731eca4c643bf7156cb6a2fee60b079577d4732e6
                     0x64974dc7ff588a0b38e37da6b767b91d068924526dd8698f131b6f19b309065aab861b33411675781d9d42b63935c85
                     0x16048641e0249a5ff6cb1b4a8c9194589148c1903b800752d8a6c09867508952d14fecb015cc4f337372b29bc32b08b1
                     0x172f08bfdf8fca06c461c9978e8d8f7de5126a9ee74d086a82d90545d9180e3f9199a7fd2fbd022a9bcfa833ec321e0a
    let leftSide = pairing <$> p1 <*> q1
    let p2 = g1Point 0x19097e1378ae74067593c7e6b71fc8ec41d11e8e1b67b9ca47475e2eb02d5959cfb4bb09a3cb4c7fc14506629b4176d1
                     0xe41648923fc4a39b9e0e0f3d4b0fdcae45caad07622e2d40e67d2eea13bff92f071c0cf4b6687417efdadfae4fec00a
    let q2 = g2Point 0xda18340291cbdd3cfaf596d62fe88f4cf211e8a2439f736786c12fba4e66cccb9279ef1a814d81785bec778c60f9284
                     0xa1d6930cfb119d6b2c52f8260217bf7859437e6aa8b8ca891ce74886f7c667274507b6f107a0c4c7618fe2f3571fcb2
                     0x9745aac53daa7296110ad436829ec3cfd8fbc83012878608479a11caf2ada57c95dd64fd5fd3d4cf3cdf536defd288
                     0x1831856291ad777b5e8f2eff3c2a4efe23a56f44ad97cda5c77f5a9c51bef1e13691011ab1979568363f5b1fecdd32d6
    let rightSide = pairing <$> p2 <*> q2
    HU.assertBool "bad pairing points" (leftSide == rightSide)


huTstPairingMul :: TestTree
huTstPairingMul = HU.testCase "huTstPairingMul" $
  do
    let p_12p34m56 = g1Generator >>= pointMul ((12 + 34) * 56)
    let q_78 = g2Generator >>= pointMul 78
    let leftSide = Control.Monad.join (pairing <$> p_12p34m56 <*> q_78)
    let p_78 = g1Generator >>= pointMul 78
    let q_12m56 = g2Generator >>= pointMul (12 * 56)
    let q_34m56 = g2Generator >>= pointMul (34 * 56)
    let pair2 = join (pairing <$> p_78 <*> q_12m56)
    let pair3 = join (pairing <$> p_78 <*> q_34m56)
    let rightSide = (*) <$> pair2 <*> pair3
    HU.assertBool "bad pairing mul" (((==) <$> leftSide <*> rightSide) == Just True)


huTstPairingAgg :: TestTree
huTstPairingAgg = HU.testCase "huTstPairingAgg" $
  do
    let p_12p34p56 = g1Generator >>= pointMul (12 + 34 + 56)
    let q_78 = g2Generator >>= pointMul 78
    let leftSide = Control.Monad.join (pairing <$> p_12p34p56 <*> q_78)
    let p_78 = g1Generator >>= pointMul 78
    let q_12 = g2Generator >>= pointMul 12
    let q_34 = g2Generator >>= pointMul 34
    let q_56 = g2Generator >>= pointMul 56
    let q_12p34 = pointAdd <$> q_12 <*> q_34
    let pair2 = join (pairing <$> p_78 <*> q_12p34)
    let pair3 = join (pairing <$> p_78 <*> q_56)
    let rightSide = (*) <$> pair2 <*> pair3
    HU.assertBool "bad pairing agg" (((==) <$> leftSide <*> rightSide) == Just True)


huTstPairingGen :: TestTree
huTstPairingGen = HU.testCase "huTstPairingGen" $
  do
    let scalar_1 = [100..102]
    let scalar_2 = [200..202]
    let p_g1 = [g1Generator >>= pointMul x | x <- scalar_1]
    let p_g2 = [g2Generator >>= pointMul x | x <- scalar_1]
    let q_g1 = [g1Generator >>= pointMul x | x <- scalar_2]
    let q_g2 = [g2Generator >>= pointMul x | x <- scalar_2]
    let pairing1 = [join (pairing <$> p <*> q) | p <- p_g1, q <- q_g2]
    let pairing2 = [join (pairing <$> q <*> p) | p <- p_g2, q <- q_g1]
    HU.assertBool "bad pairing gen" (all (uncurry (==)) (zip pairing1 pairing2))
