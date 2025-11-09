{
{-# LANGUAGE OverloadedStrings #-}

module Syntax.Parser where
import Syntax.Lexer
import Syntax.Util
import Types.Choreography
import Types.LocalBehavior
import Types.ChoreographyProtocolShell
import qualified Types.Choreography as CC
import Types.Simple
import Types.Rewrite
import qualified Types.Rewrite as RR
import qualified Data.Text as T
import qualified Data.Map as Map
}

%name parser
%tokentype { Token }
%error { parseError }
%monad { Alex } { >>= } { return }
%lexer { lexer } { EOF }

%token
    "Goals" { TGOALS _ }
    "secret" { TSECRET _ }
    "between" { TBETWEEN _ }
    "weakly" { TWEAKLY _ }
    "authenticates" { TAUTH _ }
    "on" { TON _ }
    ident { TATOM _ $$ }
    "(" { TPARENL _ }
    ")" { TPARENR _ }
    "{" { TBRACEL _ }
    "}" { TBRACER _ }
    "[" { TBRACKL _ }
    "]" { TBRACKR _ }
    "." { TDOT _ }
    "," { TCOMMA _ }
    "/" { TSLASH _ }
    ":=" { TASSIGN _ }
    ":" { TCOLON _ }
    ";" { TSEMICOLON _ }
    "=" { TEQ _ }
    "->" { TSEND _ }
    "+" { TPLUS _ }
    "*" { TSTAR _ }
    "<>" { TDIAMOND _ }
    "@" { TATSIGN _ }
    "new" { TNEW _ }
    "true" { TTOP _ }
    "not" { TNEG _ }
    "and" { TAND _ }
    "nil" { TNIL _ }
    "otherwise" { TOTHERWISE _ }
    "unlock" { TUNLOCK _ }
    "lock" { TLOCK _ }
    "if" { TIF _ }
    "then" { TTHEN _ }
    "else" { TELSE _ }
    "in" { TIN _ }
    "public" { TPUBLIC _ }
    "private" { TPRIVATE _ }
    "relation" { TRELATION _ }
    "Sigma0" { TSIGMA0 _ }
    "Sigma" { TSIGMA _ }
    "Functions" { TSIGMA _ }
    "Cells" { TCELLS _ }
    "Algebra" { TALGEBRA _ }
    "Equations" { TALGEBRA _ }
    "Protocol" { TPROTOCOL _ }

%left "and"
%nonassoc "not"

%%


-- ====== Protocol Description ======

protocolDescription :: {ProtocolDescription} 
    : optSigma0
      optSigma
      optAlgebra
      optCells
      "Protocol" ":" "{"
        roleList
        "}"
        choreography
        optGoals
      { let d = mkProtocolDescription $1 $2 $3 $4 $8 $10
        in d { protocolGoals = $11 } }

-- ====== Initialization ======

optSigma0 :: {Sigma}
    : "Sigma0" ":"  publicOpt privateOpt relationOpt
        { Sigma {public = $3, private = $4,  relation = $5} }
    | { mkEmptySigma }

optSigma :: {Sigma}
    : "Sigma" ":"  publicOpt privateOpt relationOpt
        { Sigma {public = $3, private = $4,  relation = $5} }
    | "Functions" ":" publicOpt privateOpt relationOpt
        { Sigma { public = $3, private = $4, relation = $5 } }
    | { mkEmptySigma }

publicOpt :: {Knowledge}
    : "public" knowledgeList {Map.fromList $2}
    | {Map.empty}

privateOpt :: {Knowledge}
    : "private" knowledgeList {Map.fromList $2}
    | { Map.empty }

relationOpt :: {Knowledge}
    : "relation" knowledgeList {Map.fromList $2}
    | {Map.empty}

knowledgeList :: {[(Identifier, Int)]}
    : knowledge knowledgeList {$1 : $2}
    | knowledge {$1 : []}

knowledge :: {(Identifier, Int)}
    : identifier "/" identifier {($1, read (T.unpack $3) :: Int)}

optAlgebra :: {RewriteRules}
    : "Algebra" ":" algebraList {Map.fromList $3}
    | "Equations" ":" algebraList {Map.fromList $3}
    | {Map.empty}

algebraList :: {[(Function, RewriteRule)]}
    : algebra algebraList {$1 : $2}
    | algebra {$1 : []}

algebra :: {(Function, RewriteRule)}
    : function "(" rewritePattern ")" "->" rewriteTerm {($1, ($3, $6))}

rewritePattern :: {Pattern}
    : rewriteTerm "," rewritePattern {$1 : $3}
    | rewriteTerm {$1 : []}

rewriteTermList :: {[RewriteTerm]}
    : rewriteTerm "," rewriteTermList {$1 : $3}
    | rewriteTerm {$1 : []}

rewriteTerm :: {RewriteTerm}
    : function "(" rewriteTermList ")" {RR.Comp $1 $3}
    | variable {RewriteVar (RR.UnDef $1)}


optCells :: {Map.Map Cell (Term, Term)}
    : "Cells" ":" cellList {Map.fromList $3}
    | {Map.empty}

cellList :: {[(Cell, (Term, Term))]}
    : cellInit cellList { $1 : $2 }
    | { [] }

cellInit :: {(Cell, (Term, Term))}
    : cell "[" term "]" ":=" term { ($1, ($3, $6)) }

roleList :: {[(Agent, RoleInfo)]}
    : role roleList {$1 : $2}
    | role {$1 : []}

role :: {(Agent, RoleInfo)}
    : agent ":" termList { ($1, RoleInfo { roleKnowledge = $3, roleChoice = Nothing }) }
    | mode agent "in" domain ":" termList { ($2, RoleInfo { roleKnowledge = $6, roleChoice = Just ($1, $4) }) }


-- ====== CHOREOGRAPHY Rules ======

choreography :: {Choreography}
    : "nil" {Nil}
    | "lock" "(" agent ")" "." atomic {Lock $3 $6}
    | "@" "[" stateList "]" choreography {StateHint (Map.fromList $3) $5}
    | "(" interaction ")" {$2}
    | interaction {$1}

stateList :: {[(Agent, [Term])]}
    : agent ":=" termList ";" stateList {($1, $3) : $5}
    | agent ":=" termList {($1, $3) : []}

interaction :: {Choreography}
    : agent "->" agent ":" "{" termChoreoList "otherwise" "." choreography "}"
        {Interaction $1 $3 $6 (Otherwise $9)}
    | agent "->" agent ":" "{" termChoreoList "}"
        {Interaction $1 $3 $6 Epsilon}
    | agent "->" agent ":" termList "." choreography
        {Interaction $1 $3 [(sendTermSyntacticSugar $5, $7)] Epsilon}

termChoreoList :: {[(Term, Choreography)]}
    : termList "." choreography "+" termChoreoList
        {(sendTermSyntacticSugar $1, $3) : $5}
    | termList "." choreography
        {(sendTermSyntacticSugar $1, $3) : []}

atomic :: {Atomic}
    : "new" variable "." atomic {Nonce $2 $4}
    | variable ":=" cell "[" term "]" "." atomic {Read $1 $3 $5 $8}
    | cell "[" term "]" ":=" term "." atomic {Write $1 $3 $6 $8}
    | "if" term "=" term "then" atomic "else" atomic {If $2 $4 $6 $8}
    | mode variable "in" domain "." atomic {Choice $1 $2 $4 $6}
    | mode formula "." atomic {Release $1 $2 $4}
    | "unlock" "." choreography {Unlock $3}

mode :: {Mode}
    : "*" {Star}
    | "<>" {Diamond}

formula :: {CC.Formula}
    : "true" {CC.Top}
    | term "=" term {CC.Equality $1 $3}
    | "not" formula {CC.Neg $2}
    | formula "and" formula {CC.And $1 $3}
    | "(" formula ")" {$2}

domain :: {Domain}
    : "{" variableList "}" {$2}

term :: {Term}
    : function "(" termList ")" {CC.Composed $1 $3}
    | variable {CC.Atomic $1}

termList :: {[Term]}
    : term "," termList {$1 : $3}
    | term {$1 : []}

cell :: {Cell}
    : identifier {$1}

function :: {Function}
    : identifier {fromText $1}

variable :: {Variable}
    : identifier {$1}

variableList :: {[Variable]}
    : variable "," variableList {$1 : $3}
    | variable {$1 : []}

agent :: {Agent}
    : identifier {$1}

identifier :: {Identifier}
    : ident {T.pack $1}

------- Goals ------
optGoals :: {[SecurityGoal]}
    : "Goals" ":" goalLines { $3 }
    | { [] }

goalLines :: {[SecurityGoal]}
    : goalLine goalLines { $1 : $2 }
    | goalLine { [$1] }

goalLine :: {SecurityGoal}
    : term "secret" "between" agentList
        { Secrecy $1 $4 }

    | agent "weakly" "authenticates" agent "on" term
        { WeakAuth $1 $4 $6}

    | agent "authenticates" agent "on" term
        { StrongAuth $1 $3 $5 }

agentList :: {[Agent]}
    : agent "," agentList { $1 : $3 }
    | agent { [$1] }
---------------------------------

{
-- | Rewrites the syntactic sugar of combining multiple messages.
sendTermSyntacticSugar :: [Term] -> Term
sendTermSyntacticSugar [] = error "Term list cannot be empty"
sendTermSyntacticSugar [x] = x
sendTermSyntacticSugar (x:y:ls) =
    CC.Composed PAIR [x, sendTermSyntacticSugar (y:ls)]

-- | Parsing error handler.
parseError :: Token -> Alex a
parseError tk =
    alexError $
            "Parse error at line " ++ show l ++ ", column " ++ show c
             ++ "\n  Unexpected token: " ++ show tk
    where AlexPn _ l c = token_posn tk

-- | Lexer function.
lexer :: (Token -> Alex a) -> Alex a
lexer = (alexMonadScan >>=)
}