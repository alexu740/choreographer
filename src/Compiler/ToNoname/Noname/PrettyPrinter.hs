{-# LANGUAGE OverloadedStrings #-}

module Compiler.ToNoname.Noname.PrettyPrinter where

import qualified Data.Text as T
import Compiler.ToNoname.Noname.Syntax (CenterProcess (..), Formula (..), LeftProcess (..), Mode (..), Process (..), RightProcess (..), Term (..))

class Pretty a where
  pretty :: a -> T.Text
  prettyWithIndentation :: Int -> a -> T.Text
  prettyWithIndentation _ = pretty

instance Pretty T.Text where
  pretty = id

instance (Pretty a, Pretty b) => Pretty (Term a b) where
  pretty (Atom b) = pretty b
  pretty (Comp a bs) =
    T.concat
      [ pretty a,
        "(",
        T.intercalate ", " (map pretty bs),
        ")"
      ]

instance Pretty Formula where
  pretty Top = "true"
  pretty (Equality m1 m2) =
    T.concat [pretty m1, " = ", pretty m2]
  pretty (Relational r ms) =
    T.concat [pretty r, "(", T.intercalate ", " (map pretty ms), ")"]
  pretty (Neg f) =
    T.concat ["not ", pretty f]
  pretty (And f1 f2) =
    T.concat [pretty f1, " and ", pretty f2]

instance Pretty Mode where
  pretty Star = "*"
  pretty Diamond = "<>"

instance Pretty LeftProcess where
  pretty = prettyWithIndentation 0
  prettyWithIndentation i (Choice mode var dom lp) =
    T.concat
      [ computeIndentation i,
        pretty mode,
        pretty var,
        " in ",
        "{",
        T.intercalate ", " (map pretty dom),
        "}",
        ".\n",
        prettyWithIndentation i lp
      ]
  prettyWithIndentation i (Receive var lp) =
    T.concat
      [ computeIndentation i,
        "receive ",
        pretty var,
        ".\n",
        prettyWithIndentation i lp
      ]
  prettyWithIndentation i (Center cp) = prettyWithIndentation i cp

instance Pretty CenterProcess where
  pretty = prettyWithIndentation 0
  prettyWithIndentation i (Try var f args cp1 cp2) =
    T.concat
      [ computeIndentation i,
        "try ",
        pretty var,
        ":=",
        pretty f,
        "(",
        T.intercalate ", " (map pretty args),
        ") in\n",
        prettyWithIndentation (i + 1) cp1,
        "\n",
        computeIndentation i,
        "catch ",
        pretty cp2
      ]
  prettyWithIndentation i (Read var cell msg cp) =
    T.concat
      [ computeIndentation i,
        pretty var,
        " := ",
        pretty cell,
        "[",
        pretty msg,
        "]",
        ".\n",
        prettyWithIndentation i cp
      ]
  prettyWithIndentation i (If f cp1 cp2) =
    T.concat
      [ computeIndentation i,
        "if ",
        pretty f,
        " then\n",
        prettyWithIndentation (i + 1) cp1,
        "\n",
        computeIndentation i,
        "else\n",
        prettyWithIndentation (i + 1) cp2
      ]
  prettyWithIndentation i (New vars rp) =
    if null vars
      then prettyWithIndentation i rp
      else
        T.concat
          [ computeIndentation i,
            "new ",
            T.intercalate ", " (map pretty vars),
            ".\n",
            prettyWithIndentation i rp
          ]

instance Pretty RightProcess where
  pretty = prettyWithIndentation 0
  prettyWithIndentation i (Send msg rp) =
    T.concat
      ( [ computeIndentation i,
          "send ",
          pretty msg
        ]
          ++ case rp of
            Nil -> [". ", pretty Nil]
            Sequence lp -> [". nil\n", computeIndentation i, ";\n", prettyWithIndentation i lp]
            _ -> [".\n", prettyWithIndentation i rp]
      )
  prettyWithIndentation i (Write cell msg1 msg2 rp) =
    T.concat
      [ computeIndentation i,
        pretty cell,
        "[",
        pretty msg1,
        "] := ",
        pretty msg2,
        ".\n",
        prettyWithIndentation i rp
      ]
  prettyWithIndentation i (Release mode f rp) =
    T.concat
      [ computeIndentation i,
        "release ",
        pretty mode,
        " ",
        pretty f,
        ".\n",
        prettyWithIndentation i rp
      ]
  prettyWithIndentation i Nil = computeIndentation i `T.append` "nil"
  prettyWithIndentation i (Sequence lp) =
    T.concat
      [ computeIndentation i,
        "nil ;\n",
        prettyWithIndentation i lp
      ]

instance Pretty Process where
  pretty (Pl lp) = pretty lp
  pretty (Pc cp) = pretty cp
  pretty (Pr rp) = pretty rp

computeIndentation :: Int -> T.Text
computeIndentation i = T.replicate i $ "  "
