{-# LANGUAGE OverloadedStrings #-}

module Compiler.ToNoname.Noname.FilePrinter where

import Types.Choreography (Agent, Term (..))
import Types.Simple (FUNCTIONS)
import Types.Rewrite (RewriteRule, RewriteRules)
import Choreography.State (rewriteTermToText)
import Data.List (intercalate)
import qualified Data.Map as Map
import qualified Data.Text as T
import Compiler.ToNoname.Noname.PrettyPrinter (Pretty (prettyWithIndentation))
import Compiler.ToNoname.Noname.Syntax (Process)
import Types.ChoreographyProtocolShell (InitCells, Knowledge, ProtocolDescription (..), Sigma (..))
import Syntax.Util (toText)

printToFile :: String -> ProtocolDescription -> [(Agent, Process)] -> String
printToFile filename protocolDescription transactions =
  concat
    [ header (filename ++ ".choreo"),
      "\n\n",
      printSigma True (protocolSigma0 protocolDescription),
      printSigma False (protocolSigma protocolDescription),
      printAlgebra (protocolAlgebra protocolDescription),
      printInitCells (protocolCells protocolDescription),
      printTransactions transactions,
      "\nBound: 7\n"
    ]

header :: String -> String
header filename =
  let space = 45
      filename' = take space filename ++ replicate (space - length filename - 2) ' '
   in intercalate
        "\n"
        [ "# SPDX-FileCopyrightText: 2025 Technical University of Denmark",
          "#",
          "# SPDX-License-Identifier: BSD-3-Clause",
          "",
          "############################################################################",
          "# Generated from Choreography: " ++ filename' ++ " #",
          "############################################################################"
        ]

printSigma :: Bool -> Sigma -> String
printSigma isZero (Sigma {public = pu, private = pr, relation = r})
  | null pu, null pr, null r = ""
  | otherwise =
      let name = "Sigma" ++ (if isZero then "0" else "") ++ ":\n"
          printIfNotNull str x =
            if null x
              then ""
              else "  " ++ str ++ printKnowledge x ++ "\n"
       in unwords
            [ name,
              printIfNotNull "public " pu,
              printIfNotNull "private " pr,
              printIfNotNull "relation " r,
              "\n"
            ]

printKnowledge :: Knowledge -> String
printKnowledge =
  unwords
    . map (\(ident, num) -> T.unpack ident ++ "/" ++ show num)
    . Map.toList

printAlgebra :: RewriteRules -> String
printAlgebra rwRules
  | Map.null rwRules = ""
  | otherwise =
      concat
        [ "Algebra:\n",
          unlines (map printRewriteRule (Map.toList rwRules)),
          "\n"
        ]

printRewriteRule :: (FUNCTIONS, RewriteRule) -> String
printRewriteRule (func, (pattern, replacement)) =
  "  "
    ++ T.unpack
      ( T.concat
          [ toText func,
            "(",
            T.intercalate "," (map rewriteTermToText pattern),
            ")",
            "->",
            rewriteTermToText replacement
          ]
      )

printInitCells :: InitCells -> String
printInitCells initCells
  | null initCells = ""
  | otherwise =
      "Cells:\n"
        ++ ( intercalate
               "\n"
               . Map.elems
               . Map.mapWithKey
                 ( \cell (t1, t2) ->
                     concat
                       [ "  ",
                         T.unpack cell,
                         "[",
                         printTerm t1,
                         "]",
                         ":=",
                         printTerm t2
                       ]
                 )
               $ initCells
           )
        ++ "\n\n"

printTerm :: Term -> String
printTerm (Atomic l) = T.unpack l
printTerm (Composed f ls) = T.unpack (toText f) ++ "(" ++ intercalate ", " (map printTerm ls) ++ ")"

printTransactions :: [(Agent, Process)] -> String
printTransactions = intercalate "\n" . map printTransaction

printTransaction :: (Agent, Process) -> String
printTransaction (agent, process) =
  let top = "Transaction " ++ T.unpack agent ++ ":\n"
   in top ++ T.unpack (prettyWithIndentation 0 process) ++ "\n"
