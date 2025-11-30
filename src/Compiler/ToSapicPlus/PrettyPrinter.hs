{-# LANGUAGE OverloadedStrings #-}
module Compiler.ToSapicPlus.PrettyPrinter where

import Types.Choreography
import Types.Sapic
import Types.Simple
import Syntax.Util(toText)
import Data.Char (toLower)
import qualified Data.Text as T
import qualified Data.Set as Set
import Data.List (intercalate, stripPrefix)

prettySProtocol :: SProtocol -> String
prettySProtocol (SProtocol header agents mainP lemmas queries) =
  unlines $
    [ "theory " <> T.unpack (theory header)
    , "begin"
    ]
    ++ renderBuiltins (builtins header)
    ++ renderFunctions (builtins header) (functions header)
    ++ renderEquations (equations header)
    ++ concat (zipWith ppAgent [1 :: Int ..] agents)
    ++ lines (prettyMainProcess 1 "process" mainP)
    ++ concatMap (lines . ppLemma) lemmas
    ++ renderQueries queries
    ++ ["end"]
  where
    ppAgent :: Int -> SAgentProcess -> [String]
    ppAgent i (SAgentProcess { processName = nm
                             , processHeader = params
                             , processBody = body 
                             }) =
      lines (prettyProcess 0 (agentTitle i nm params) body)

    agentTitle :: Int -> T.Text -> [T.Text] -> String
    agentTitle i nm params =
      "let " ++ T.unpack nm ++ renderParams params

    renderBuiltins [] = []
    renderBuiltins xs =
      ["builtins: " <> intercalate ", " (map renderBuiltinSymbol xs)]
    
    renderBuiltinSymbol :: BuiltinTheory -> String
    renderBuiltinSymbol Hashing = "hashing"
    renderBuiltinSymbol AsymmetricEncryption = "asymmetric-encryption"
    renderBuiltinSymbol Signing = "signing"
    renderBuiltinSymbol RevealingSigning = "revealing-signing"
    renderBuiltinSymbol SymmetricEncryption = "symmetric-encryption"
    renderBuiltinSymbol DiffieHellman = "diffie-hellman"

    renderFunctions :: [BuiltinTheory] -> [SProtocolHeaderFunction] -> [String]
    renderFunctions _ [] = []
    renderFunctions theories fs =
      case filtered of
        [] -> []
        _ -> [ T.unpack ("functions: " <> T.intercalate ", " (map renderOne filtered)) ]
      where
        builtinSet :: Set.Set T.Text
        builtinSet = Set.fromList . concatMap builtinNames $ theories

        builtinNames :: BuiltinTheory -> [T.Text]
        builtinNames t = case t of
          Hashing -> [T.pack "h/1"]
          AsymmetricEncryption -> map T.pack ["aenc/2","adec/2","pk/1"]
          Signing -> map T.pack ["sign/2","verify/3","pk/1", "true/0"]
          RevealingSigning -> map T.pack ["revealsign/2","revealverify/3","getmessage/1","pk/1"]
          SymmetricEncryption -> map T.pack ["senc/2","sdec/2"]
          DiffieHellman -> map T.pack ["mult/2","exp/2"]

        isBuiltin :: T.Text -> Bool
        isBuiltin name = T.toLower name `Set.member` builtinSet

        filtered :: [SProtocolHeaderFunction]
        filtered = filter (\(name, _isPublic) -> not (isBuiltin name)) fs

        renderOne :: SProtocolHeaderFunction -> T.Text
        renderOne (fname, isPublic) =
          let base = T.toLower fname
          in if isPublic then base else base <> " [private]"

    renderEquations :: [Rule] -> [String]
    renderEquations [] = []
    renderEquations rs = do
      "equations:" : map (("  " ++) . renderRule) rs
      where
        renderRule :: Rule -> String
        renderRule (Rule f as res) =
          ppFun f ++ "(" ++ intercalate ", " (map ppRTerm as) ++ ") = " ++ ppRTerm res

        ppFun :: Function -> String
        ppFun (UnDef x) = map toLower (T.unpack x)
        ppFun x = map toLower (show x)

        ppRTerm :: RTerm -> String
        ppRTerm (RConstr f1 args) = ppFun f1 ++ "(" ++ intercalate ", " (map ppRTerm args) ++ ")"
        ppRTerm (RVar x) = map toLower (T.unpack x)

    renderParams :: [T.Text] -> String
    renderParams [] = "()"
    renderParams xs = "(" ++ intercalate ", " (map T.unpack xs) ++ ")"


---
prettyProcess :: Int -> String -> SProcess -> String
prettyProcess ind label p =
  unlines $ (indent ind <> label <> " =") : prettyProcLines (ind + 1) p

prettyMainProcess :: Int -> String -> SProcess -> String
prettyMainProcess ind label p =
  unlines $ (label <> ": ") : prettyProcLines ind p

intercalateLines :: [String] -> [[String]] -> [String]
intercalateLines = intercalate

prettyProcLines :: Int -> SProcess -> [String]
prettyProcLines ind p = case p of
  SNil ->
    line ind "0"

  SIn v cont ->
    line ind ("in(" <> ppTerm v <> ");")
    ++ prettyProcLines ind cont

  SNew n cont ->
    line ind ("new " <> ppTerm n <> ";")
    ++ prettyProcLines ind cont

  SOut branches ->
    case branches of
      [] ->
        line ind "out { }"
      [(t, cont)] ->
        line ind ("out(" <> ppTerm t <> ");")
        ++ prettyProcLines ind cont

  SLet pat scr pThen pElse ->
    blockWith ind ("let " <> ppPattern pat <> " = " <> ppTerm scr <> " in") $ \ind' ->
      prettyProcLines ind' pThen
    ++ case pElse of
         SNil -> []
         _ -> blockWith ind "else" $ \ind' -> prettyProcLines ind' pElse

  SIf t1 t2 pThen pElse ->
    blockWith ind ("if " <> ppTerm t1 <> " = " <> ppTerm t2 <> " then") $ \ind' ->
      prettyProcLines ind' pThen
    ++ case pElse of
         SNil -> []
         _ -> blockWith ind "else" $ \ind' ->
                   prettyProcLines ind' pElse

  SChoice t1 t2 pThen pElse ->
    blockWith ind ("if " <> ppTerm t1 <> " = '" <> T.unpack t2 <> "' then") $ \ind' ->
      prettyProcLines ind' pThen
    ++ case pElse of
         SNil -> []
         _ -> blockWith ind "else" $ \ind' ->
                   prettyProcLines ind' pElse

  SReplication p ->
    prefixOpOnFirst ind "!" (prettyProcLines ind p)

  SParallel [] ->
    line ind "()"

  SParallel [p] ->
    block ind "(" (prettyProcLines (ind+1) p)
    ++ line ind ")"

  SFact factType terms p ->
    (indent ind <> "event " <> show factType
      <> "(" <> intercalate ", " (map ppFactArguments terms) <> ");")
    : prettyProcLines ind p

  SParallel ps ->
    let rendered = map (prettyProcLines (ind+1)) ps
        sepLine  = line ind " | "
    in line ind "("
        ++ intercalateLines sepLine rendered
        ++ line ind ")"

  SAgentInitialisation s terms ->
    line ind (T.unpack s <> "(" <> intercalate ", " (map ppTerm terms) <> ")")
  
  SInsert key value next ->
    let keyStr = ppTerm key
        valStr = ppTerm value
        thisLine = indent ind <> "insert " <> keyStr <> ", " <> valStr <> ";"
    in thisLine : prettyProcLines ind next

  SLookup key var pThen pElse ->
    let pad = replicate ind ' '
        keyStr = ppTerm key
        line1 = indent ind <> "lookup " <> keyStr <> " as " <> T.unpack var <> " in"
        thenLines = prettyProcLines (ind + 1) pThen
        lineElse = indent ind <> "else"
        elseLines = prettyProcLines (ind + 1) pElse
    in line1 : thenLines ++ [lineElse] ++ elseLines

-- helpers
ppFactArguments :: SFactArgument -> String
ppFactArguments trm = case trm of
  SFTerm n -> ppTerm n
  SFConst v -> "'" ++ T.unpack v ++ "'"

ppTerm :: STerm -> String
ppTerm trm = case trm of
  TName n -> ppName n
  TVariable v -> ppVar v
  TFunction (UnDef f) [] -> T.unpack f <> "()"
  TFunction f [] -> ppFun f <> "()"
  TFunction (UnDef f) ts -> T.unpack f <> "(" <> commaSep (map ppTerm ts) <> ")"
  TFunction f ts -> ppFun f <> "(" <> commaSep (map ppTerm ts) <> ")"

ppPattern :: SPattern -> String
ppPattern trm = case trm of
  PVar v -> ppVar v
  PTerm t -> ppTerm t
  PData f args -> ppFun f <> "(" <> ppPatArgs args <> ")"
  where
    ppPatArgs :: [SPatternArg] -> String
    ppPatArgs = commaSep . map ppArg

    ppArg :: SPatternArg -> String
    ppArg arg = case arg of
      PBind v -> ppTerm v
      PCompare t -> "=" <> ppTerm t

ppName :: SName -> String
ppName = T.unpack 

ppVar :: SVariable -> String
ppVar = T.unpack

ppFun :: Function -> String
ppFun = T.unpack . toText

commaSep :: [String] -> String
commaSep [] = ""
commaSep (x:xs) = x ++ concatMap (", " ++) xs

indent :: Int -> String
indent n = replicate (2*n) ' '

line :: Int -> String -> [String]
line ind s = [indent ind <> s]

block :: Int -> String -> [String] -> [String]
block ind hdr body =
  line ind hdr ++ body

blockWith :: Int -> String -> (Int -> [String]) -> [String]
blockWith ind hdr k =
  line ind hdr ++ k (ind+1)


prefixFirst :: String -> [String] -> [String]
prefixFirst p ss = case ss of
  [] -> [p]
  (l:ls) -> (p <> l) : ls

prefixOpOnFirst :: Int -> String -> [String] -> [String]
prefixOpOnFirst ind op s = case s of
  [] -> [indent ind <> op <> " 0"]
  (l:ls) ->
    let pre = indent ind
        body = maybe l id (stripPrefix pre l)
    in (pre <> op <> " " <> body) : ls

ppLemma :: Lemma -> String
ppLemma (Lemma nm out ex body) =
  "lemma " <> T.unpack nm 
  <> renderOutputs out
  <> (if ex then " : exists-trace\n  \"" else " :\n  \"")
  <> ppF body 
  <> "\""
  where
    ppF x = case x of
      FFact p xs t -> 
        let xs' = quoteGoalIdIfNeeded p xs
        in ppPred p <> "(" <> intercalate ", " (map T.unpack xs') <> ") @ " <> ppSym t
      FNot f -> "not(" <> ppF f <> ")"
      FAnd a b -> "(" <> ppF a <> " & "  <> ppF b <> ")"
      FOr a b -> "(" <> ppF a <> " | "  <> ppF b <> ")"
      FImply a b -> "(" <> ppF a <> " ==> " <> ppF b <> ")"
      FForall vs f -> "All " <> unwords (map T.unpack vs) <> ". " <> ppF f
      FExists vs f -> "Ex "  <> unwords (map T.unpack vs) <> ". " <> ppF f
      FEq x y -> T.unpack x <> " = " <> T.unpack y
    
    quoteGoalIdIfNeeded :: LFact -> [Symbol] -> [Symbol]
    quoteGoalIdIfNeeded PRequest (a2:a1:gid:rest) =
      a2 : a1 : quote gid : rest
    quoteGoalIdIfNeeded PWitness (a1:a2:gid:rest) =
      a1 : a2 : quote gid : rest
    quoteGoalIdIfNeeded _ xs = xs

    quote :: T.Text -> T.Text
    quote s = T.concat ["'", s, "'"]

    ppPred c = case c of
      PSecret -> "Secret"
      PWitness -> "Witness"
      PRequest -> "Request"
      PIntruderKnows -> "KU"
      PHonest -> "Honest"

    renderOutputs :: [LemmaOutput] -> String
    renderOutputs os =
      case [pp | o <- os, let pp = ppLemOut o, not (null pp)] of
        [] -> ""
        xs -> " [output=[" <> intercalate ", " xs <> "]]"

    ppLemOut :: LemmaOutput -> String
    ppLemOut Spthy = "spthy"
    ppLemOut Proverif = "proverif"

    ppSym :: Symbol -> String
    ppSym s =
      let raw = T.unpack s
      in case raw of
          ('#':rest) -> rest
          _ -> raw

renderQueries :: [ProverifQuery] -> [String]
renderQueries [] = []
renderQueries qs =
  [ "export queries :"
  , " \""
  ]
  ++ map ((" " ++) . ppPVQuery) qs
  ++ [ " \"" ]

ppPVQuery :: ProverifQuery -> String
ppPVQuery (ProverifQuery args body) =
  "query " <> commaSep [ T.unpack v <> ":" <> T.unpack ty | (v, ty) <- args ] <> "; "
  <> ppPV body <> "."

ppPV :: ProverifFormula -> String
ppPV frm = case frm of
  PVEvent f xs -> "event(" <> ppPVAtom f xs <> ")"
  PVInjEvent f xs -> "inj-event(" <> ppPVAtom f xs <> ")"
  PVAnd a b -> "(" <> ppPV a <> " && " <> ppPV b <> ")"
  PVOr a b -> "(" <> ppPV a <> " || " <> ppPV b <> ")"
  PVImpl a b -> "(" <> ppPV a <> " ==> " <> ppPV b <> ")"

ppPVAtom :: LFact -> [Symbol] -> String
ppPVAtom fact xs =
  case fact of
    PIntruderKnows -> "attacker(" <> commaSep (map T.unpack xs) <> ")"
    _ -> pvPred fact <> "(" <> commaSep (map T.unpack xs) <> ")"

pvPred :: LFact -> String
pvPred fact = case fact of
  PHonest -> "eHonest"
  PDishonest -> "eDishonest"
  PRequest -> "eRequest"
  PWitness -> "eWitness"
  PSecret -> "eSecret"
  PIntruderKnows -> "attacker"