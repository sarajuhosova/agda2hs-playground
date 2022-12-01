module TypeChecker.Lang where

open import Haskell.Prelude

------------------------------------------------------------
-- TYPES                                                  --
------------------------------------------------------------

data Type : Set where
    TBool : Type
    TInt : Type

eqType : Type → Type → Bool
eqType TBool TBool = True
eqType TInt TInt = True
eqType _ _ = False

instance
  iEqType : Eq Type
  iEqType ._==_ = eqType

{-# COMPILE AGDA2HS Type #-}

------------------------------------------------------------
-- EXPRESSIONS                                            --
------------------------------------------------------------

data Expr : Set where
    EBool : Bool → Expr
    EInt  : Int  → Expr
    EAdd  : Expr → Expr → Expr
    EEq   : Expr → Expr → Expr
    ENot  : Expr → Expr
    EAnd  : Expr → Expr → Expr
    EOr   : Expr → Expr → Expr
    EIf   : Expr → Expr → Expr → Expr

eqExpr : Expr → Expr → Bool
eqExpr (EBool a) (EBool b) = a == b
eqExpr (EInt i) (EInt j) = i == j
eqExpr (EAdd left₁ right₁) (EAdd left₂ right₂) = eqExpr left₁ left₂ && eqExpr right₁ right₂
eqExpr (EEq left₁ right₁) (EEq left₂ right₂) = eqExpr left₁ left₂ && eqExpr right₁ right₂
eqExpr (ENot a) (ENot b) = eqExpr a b
eqExpr (EAnd left₁ right₁) (EAnd left₂ right₂) = eqExpr left₁ left₂ && eqExpr right₁ right₂
eqExpr (EOr left₁ right₁) (EOr left₂ right₂) = eqExpr left₁ left₂ && eqExpr right₁ right₂
eqExpr (EIf iff₁ thn₁ els₁) (EIf iff₂ thn₂ els₂) = eqExpr iff₁ iff₂ && eqExpr thn₁ thn₂ && eqExpr els₁ els₂
eqExpr _ _ = False

instance
  iEqExpr : Eq Expr
  iEqExpr ._==_ = eqExpr

{-# COMPILE AGDA2HS Expr #-}

------------------------------------------------------------
-- VALUES                                                 --
------------------------------------------------------------

data Val : Set where
    VBool : Bool → Val
    VInt  : Int  → Val

eqVal : Val → Val → Bool
eqVal (VBool a) (VBool b) = a == b
eqVal (VInt i) (VInt j) = i == j
eqVal _ _ = False

instance
  iEqVal : Eq Val
  iEqVal ._==_ = eqVal

{-# COMPILE AGDA2HS Val #-}

eqValType : Val → Val → Bool
eqValType (VBool _) (VBool _) = True
eqValType (VInt _) (VInt _) = True
eqValType _ _ = False

{-# COMPILE AGDA2HS eqValType #-}
