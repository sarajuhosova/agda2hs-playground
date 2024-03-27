module TypeCheck.Examples where

import Test.QuickCheck
import TypeCheck.Lang
import Util.Scope
import TypeCheck.Context
import TypeCheck.Type (Type(TyNat, TyArr))
import TypeCheck.TypeChecker (inferType, checkType)
import TypeCheck.TypingRules (TyTerm(TyApp, TyTVar))

exampleTerm :: Term
exampleTerm = TApp (TVar Here) (TVar (There Here))

exampleContext :: Context
exampleContext = CtxExtend (CtxExtend CtxEmpty TyNat) (TyArr TyNat TyNat)

exampleInfer :: Bool
exampleInfer = 
  case inferType exampleContext exampleTerm of
    Right (t, _) -> t == TyNat
    Left _ -> False

exampleCheck :: Bool
exampleCheck = 
  case checkType exampleContext exampleTerm TyNat of
    Right _ -> True
    Left _ -> False

runExamples :: IO ()
runExamples = do
  quickCheck exampleInfer
  quickCheck exampleCheck

