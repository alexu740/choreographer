module Compiler.ToSapicPlus.RewriteSystem.RewriteReceipt where

import Types.Simple (Function)
import Types.Sapic (SVariable, STerm(..), SRecipe(..), SapicTranslationError, Rule, RTerm)
import Types.Choreography (Term(..))

data RewriteReceipt
  = RewriteReceipt
  { frameKey :: SVariable,
    subject :: Term,
    rule :: Rule,
    subjectRecipe :: SVariable,
    ruleFunction :: Function,
    ruleArgsToTermsMap :: [(RTerm, Term)],
    ruleArgsToRecipeMap :: [(RTerm, STerm)]
  }
  deriving (Show, Eq)