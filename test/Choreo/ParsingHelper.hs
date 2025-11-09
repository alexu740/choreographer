{-# OPTIONS_GHC -Wno-orphans #-}

module Choreo.ParsingHelper where

import Types.Choreography (Atomic (..), CDefault (..), Choreography (..), Formula (..), Term (..))
import Types.Simple (FUNCTIONS (..), Mode (..))
import Syntax.Util (toText)
import Data.List (intercalate)
import qualified Data.Text as T
import Test.QuickCheck (Arbitrary (arbitrary), Gen, choose, elements, listOf, listOf1, oneof, sized, suchThat, vectorOf)

instance Arbitrary T.Text where
  arbitrary = do
    firstC <- oneof [choose ('a', 'h'), choose ('j', 'z')]
    restC <- listOf . elements $ ['a' .. 'z'] ++ ['A' .. 'Z'] ++ ['0' .. '9'] ++ ['_']
    return $ T.pack [firstC] `T.append` T.pack restC

instance Arbitrary FUNCTIONS where
  arbitrary =
    oneof
      [ pure SCRYPT,
        pure CRYPT,
        pure SIGN,
        pure PAIR,
        pure HASH,
        UnDef <$> arbitrary
      ]

instance Arbitrary Term where
  arbitrary = sized genTerm

genTerm :: Int -> Gen Term
genTerm 0 = Atomic <$> arbitrary
genTerm n =
  oneof
    [ Atomic <$> arbitrary,
      do
        f <- arbitrary
        ar <- choose (1, 3) -- limit function arity
        args <- vectorOf ar (genTerm (n `div` (ar + 1)))
        return $ Composed f args
    ]

instance Arbitrary Formula where
  arbitrary = sized genFormula

genFormula :: Int -> Gen Formula
genFormula 0 = return Top
genFormula n =
  oneof
    [ return Top,
      Equality <$> genTerm (n `div` 2) <*> genTerm (n `div` 2),
      Neg <$> genFormula (n `div` 2),
      And <$> genFormula (n `div` 2) <*> genFormula (n `div` 2)
    ]

instance Arbitrary Mode where
  arbitrary = elements [Star, Diamond]

instance Arbitrary Atomic where
  arbitrary = sized genAtomic

genAtomic :: Int -> Gen Atomic
genAtomic 0 = pure (Unlock Nil)
genAtomic n =
  oneof
    [ Nonce <$> arbitrary <*> genAtomic (n `div` 2),
      Read <$> arbitrary <*> arbitrary <*> genTerm (n `div` 3) <*> genAtomic (n `div` 2),
      Write <$> arbitrary <*> genTerm (n `div` 3) <*> genTerm (n `div` 3) <*> genAtomic (n `div` 2),
      If <$> genTerm (n `div` 3) <*> genTerm (n `div` 3) <*> genAtomic (n `div` 2) <*> genAtomic (n `div` 2),
      Choice <$> arbitrary <*> arbitrary <*> listOf1 arbitrary <*> genAtomic (n `div` 2),
      Release <$> arbitrary <*> genFormula (n `div` 2) <*> genAtomic (n `div` 2),
      Unlock <$> genChoreography (n `div` 2)
    ]

instance Arbitrary CDefault where
  arbitrary =
    oneof
      [ return Epsilon,
        Otherwise <$> genChoreography 1
      ]

instance Arbitrary Choreography where
  arbitrary = sized genChoreography

genChoreography :: Int -> Gen Choreography
genChoreography 0 = return Nil
genChoreography n =
  oneof
    [ return Nil,
      do
        a1 <- arbitrary
        a2 <- arbitrary `suchThat` (/= a1)
        numTerms <- choose (1, 3)
        termChorPairs <-
          vectorOf numTerms $
            (,) <$> genTerm (n `div` 4) <*> genChoreography (n `div` 2)
        Interaction a1 a2 termChorPairs <$> arbitrary,
      Lock <$> arbitrary <*> genAtomic (n `div` 2)
    ]

---------------------------------------------------------------------
-- PRETTY PRINTING
---------------------------------------------------------------------

prettyPrint :: Choreography -> String
prettyPrint Nil = "nil"
prettyPrint (Interaction a1 a2 termChoreoPairs (Otherwise cdefault)) =
  concat
    [ prettyPrintText a1,
      " -> ",
      prettyPrintText a2,
      " : ",
      "{",
      prettyPrintTermChoreoList termChoreoPairs,
      " otherwise. ",
      prettyPrint cdefault,
      "}",
      "\n"
    ]
prettyPrint (Interaction a1 a2 termChoreoPairs Epsilon) =
  concat
    [ prettyPrintText a1,
      " -> ",
      prettyPrintText a2,
      " : ",
      if length termChoreoPairs > 1
        then
          concat
            [ "{",
              prettyPrintTermChoreoList termChoreoPairs,
              "}"
            ]
        else prettyPrintTermChoreoList termChoreoPairs,
      "\n"
    ]
prettyPrint (Lock ag at) =
  concat
    [ "lock(",
      prettyPrintText ag,
      "). ",
      prettyPrintAtomic at
    ]

prettyPrintAtomic :: Atomic -> String
prettyPrintAtomic (Nonce v a) =
  concat
    [ "new ",
      prettyPrintText v,
      ". ",
      prettyPrintAtomic a
    ]
prettyPrintAtomic (Read v c t a) =
  concat
    [ prettyPrintText v,
      ":=",
      prettyPrintText c,
      "[",
      prettyPrintTerm t,
      "]. ",
      prettyPrintAtomic a
    ]
prettyPrintAtomic (Write c t1 t2 a) =
  concat
    [ prettyPrintText c,
      "[",
      prettyPrintTerm t1,
      "]",
      ":=",
      prettyPrintTerm t2,
      ". ",
      prettyPrintAtomic a
    ]
prettyPrintAtomic (If t1 t2 a1 a2) =
  concat
    [ "if ",
      prettyPrintTerm t1,
      " = ",
      prettyPrintTerm t2,
      " then ",
      prettyPrintAtomic a1,
      " else ",
      prettyPrintAtomic a2
    ]
prettyPrintAtomic (Choice m v d a) =
  concat
    [ prettyPrintMode m,
      prettyPrintText v,
      " in ",
      "{",
      intercalate ", " (map prettyPrintText d),
      "}",
      ". ",
      prettyPrintAtomic a
    ]
prettyPrintAtomic (Release m f a) =
  concat
    [ prettyPrintMode m,
      prettyPrintFormula f,
      ". ",
      prettyPrintAtomic a
    ]
prettyPrintAtomic (Unlock c) =
  "unlock. " ++ prettyPrint c

prettyPrintTermChoreoList :: [(Term, Choreography)] -> String
prettyPrintTermChoreoList [] = error "Empty term-choreography list"
prettyPrintTermChoreoList [(t, c)] = prettyPrintTermChoreo (t, c)
prettyPrintTermChoreoList tcs = intercalate " + " (map prettyPrintTermChoreo tcs)

prettyPrintTermChoreo :: (Term, Choreography) -> String
prettyPrintTermChoreo (t, c) =
  concat
    [ prettyPrintTerm t,
      ". ",
      prettyPrint c
    ]

prettyPrintTerm :: Term -> String
prettyPrintTerm (Atomic t) = prettyPrintText t
prettyPrintTerm (Composed f ts) =
  concat
    [ prettyPrintText (toText f),
      "(",
      intercalate ", " (map prettyPrintTerm ts),
      ")"
    ]

prettyPrintFormula :: Formula -> String
prettyPrintFormula Top = "true"
prettyPrintFormula (Equality t1 t2) =
  concat
    [ prettyPrintTerm t1,
      " = ",
      prettyPrintTerm t2
    ]
prettyPrintFormula (Neg f) =
  concat
    [ "not ",
      "(",
      prettyPrintFormula f,
      ")"
    ]
prettyPrintFormula (And f1 f2) =
  concat
    [ "(",
      prettyPrintFormula f1,
      ")",
      " and ",
      "(",
      prettyPrintFormula f2,
      ")"
    ]

prettyPrintMode :: Mode -> String
prettyPrintMode Star = "*"
prettyPrintMode Diamond = "<>"

prettyPrintText :: T.Text -> String
prettyPrintText = T.unpack
