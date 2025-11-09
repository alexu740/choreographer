{
module Syntax.Lexer (Token(..), AlexPosn(..), alexMonadScan, token_posn, Alex, alexError, runAlex, tokenizeAll) where
}

%wrapper "monad"

$digit = 0-9
$alpha = [a-zA-Z]
$alphaL = [a-z]
$alphaU = [A-Z]
$identChar = [a-zA-Z0-9_]
$mark = \'

tokens :-
  $white+ ;
  "#".*		;
  "(" { mkToken TPARENL }
  ")" { mkToken TPARENR }
  "{" { mkToken TBRACEL }
  "}" { mkToken TBRACER }
  "[" { mkToken TBRACKL }
  "]" { mkToken TBRACKR }
  "." { mkToken TDOT }
  "," { mkToken TCOMMA }
  "/" { mkToken TSLASH }
  ":=" { mkToken TASSIGN }
  ":" { mkToken TCOLON }
  ";" { mkToken TSEMICOLON }
  "=" { mkToken TEQ }
  "->" { mkToken TSEND }
  "+" { mkToken TPLUS }
  "*" { mkToken TSTAR }
  "<>" { mkToken TDIAMOND }
  "@" { mkToken TATSIGN }
  "new" { mkToken TNEW }
  "true" { mkToken TTOP }
  "not" { mkToken TNEG }
  "and" { mkToken TAND }
  "nil" { mkToken TNIL }
  "otherwise" { mkToken TOTHERWISE }
  "unlock" { mkToken TUNLOCK }
  "lock" { mkToken TLOCK }
  "if" { mkToken TIF }
  "then" { mkToken TTHEN }
  "else" { mkToken TELSE }
  "in" { mkToken TIN }
  "public" { mkToken TPUBLIC }
  "private" { mkToken TPRIVATE }
  "relation" { mkToken TRELATION }
  "Sigma0" { mkToken TSIGMA0 }
  "Sigma" { mkToken TSIGMA }
  "Functions" { mkToken TSIGMA }
  "Algebra" { mkToken TALGEBRA }
  "Equations" { mkToken TALGEBRA }
  "Cells" { mkToken TCELLS }
  "Protocol" { mkToken TPROTOCOL }
  "Goals" { mkToken TGOALS }
  "secret" { mkToken TSECRET }
  "between" { mkToken TBETWEEN }
  "weakly" { mkToken TWEAKLY }
  "authenticates" { mkToken TAUTH }
  "on" { mkToken TON }
  $alpha $identChar* $mark* { mkTokenStr TATOM }
  $digit+ { mkTokenStr TATOM }


{
data Token
  = TATOM AlexPosn String
  | TPARENL AlexPosn
  | TPARENR AlexPosn
  | TBRACEL AlexPosn
  | TBRACER AlexPosn
  | TBRACKL AlexPosn
  | TBRACKR AlexPosn
  | TDOT AlexPosn
  | TCOMMA AlexPosn
  | TSLASH AlexPosn
  | TASSIGN AlexPosn
  | TCOLON AlexPosn
  | TSEMICOLON AlexPosn
  | TEQ AlexPosn
  | TSEND AlexPosn
  | TPLUS AlexPosn
  | TSTAR AlexPosn
  | TDIAMOND AlexPosn
  | TNEW AlexPosn
  | TATSIGN AlexPosn
  | TTOP AlexPosn
  | TNEG AlexPosn
  | TAND AlexPosn
  | TNIL AlexPosn
  | TOTHERWISE AlexPosn
  | TUNLOCK AlexPosn
  | TLOCK AlexPosn
  | TIF AlexPosn
  | TTHEN AlexPosn
  | TELSE AlexPosn
  | TIN AlexPosn
  | TPUBLIC AlexPosn
  | TPRIVATE AlexPosn
  | TRELATION AlexPosn
  | TSIGMA0 AlexPosn
  | TSIGMA AlexPosn
  | TALGEBRA AlexPosn
  | TCELLS AlexPosn
  | TPROTOCOL AlexPosn
  | TGOALS AlexPosn
  | TSECRET AlexPosn
  | TBETWEEN AlexPosn
  | TWEAKLY AlexPosn
  | TAUTH AlexPosn
  | TON AlexPosn
  | EOF
  deriving (Eq, Show)

alexEOF :: Alex Token
alexEOF = return EOF

token_posn (TATOM p _) = p
token_posn (TPARENL p) = p
token_posn (TPARENR p) = p
token_posn (TBRACEL p) = p
token_posn (TBRACER p) = p
token_posn (TBRACKL p) = p
token_posn (TBRACKR p) = p
token_posn (TDOT p) = p
token_posn (TCOMMA p) = p
token_posn (TSLASH p) = p
token_posn (TASSIGN p) = p
token_posn (TCOLON p) = p
token_posn (TSEMICOLON p) = p
token_posn (TEQ p) = p
token_posn (TSEND p) = p
token_posn (TPLUS p) = p
token_posn (TSTAR p) = p
token_posn (TDIAMOND p) = p
token_posn (TNEW p) = p
token_posn (TATSIGN p) = p
token_posn (TTOP p) = p
token_posn (TNEG p) = p
token_posn (TAND p) = p
token_posn (TNIL p) = p
token_posn (TOTHERWISE p) = p
token_posn (TUNLOCK p) = p
token_posn (TLOCK p) = p
token_posn (TIF p) = p
token_posn (TTHEN p) = p
token_posn (TELSE p) = p
token_posn (TIN p) = p
token_posn (TPUBLIC p) = p
token_posn (TPRIVATE p) = p
token_posn (TRELATION p) = p
token_posn (TSIGMA0 p) = p
token_posn (TSIGMA p) = p
token_posn (TALGEBRA p) = p
token_posn (TCELLS p) = p
token_posn (TPROTOCOL p) = p
token_posn (TGOALS p) = p
token_posn (TSECRET p) = p
token_posn (TBETWEEN p) = p
token_posn (TWEAKLY p) = p
token_posn (TAUTH p) = p
token_posn (TON p) = p
token_posn _ = AlexPn 0 0 0

mkToken :: (AlexPosn -> Token) -> AlexInput -> Int -> Alex Token
mkToken f (p, _, _, _) _ = return (f p)

mkTokenStr :: (AlexPosn -> String -> Token) -> AlexInput -> Int -> Alex Token
mkTokenStr f (p, _, _, s) i = return (f p $ take i s)

-- | Collect all tokens from the input for debugging.
tokenizeAll :: String -> Either String [Token]
tokenizeAll input = runAlex input go
  where
    go = do
      tok <- alexMonadScan
      case tok of
        EOF -> return [EOF]
        _   -> do
          rest <- go
          return (tok : rest)
}