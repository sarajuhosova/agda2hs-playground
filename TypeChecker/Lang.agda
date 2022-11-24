module TypeChecker.Lang where

open import Haskell.Prelude

------------------------------------------------------------
-- TYPES                                                  --
------------------------------------------------------------

data Type : Set where
    TBool : Type
    TInt : Type
    TFun : Type → Type → Type

{-# COMPILE AGDA2HS Type #-}

------------------------------------------------------------
-- EXPRESSIONS                                            --
------------------------------------------------------------

data Const : Set where
    -- booleans
    ETrue : Const
    EFalse : Const
    -- zero
    EZero : Const
    -- number functions
    ESucc : Const
    EPred : Const
    EIsZero : Const

data Expr : Set where
    EConst : Const → Expr
    -- flow control
    EIf : Expr → Expr → Expr → Expr
    -- variables
    EVar : String → Expr
    -- functions
    ELam : String → Type → Expr → Expr
    -- function application
    EApp : Expr → Expr → Expr

{-# COMPILE AGDA2HS Const #-}
{-# COMPILE AGDA2HS Expr #-}

------------------------------------------------------------
-- CONTEXT                                                --
------------------------------------------------------------

data Ctx (a : Set) : Set where
    CNil : Ctx a
    CCons : String → a → Ctx a → Ctx a

findInCtx : {a : Set} → String → Ctx a → Maybe a
findInCtx x CNil = Nothing
findInCtx x (CCons c t cs) = if x == c then Just t else findInCtx x cs

{-# COMPILE AGDA2HS Ctx #-}
{-# COMPILE AGDA2HS findInCtx #-}

------------------------------------------------------------
-- VALUES                                                 --
------------------------------------------------------------

data Val : Set where
    VInt  : Int → Val
    VBool : Bool → Val
    VFun  : Expr → Val

{-# COMPILE AGDA2HS Val #-}

------------------------------------------------------------
-- EQUALITIES                                             --
------------------------------------------------------------

{- Type -}
eqType : Type → Type → Bool
eqType TBool TBool = True
eqType TInt TInt = True
eqType (TFun t t₁) (TFun s s₁) = eqType t s && eqType t₁ s₁
eqType _ _ = False

instance
  iEqType : Eq Type
  iEqType ._==_ = eqType

{- Const -}
eqConst : Const → Const → Bool
eqConst ETrue ETrue  = True
eqConst EFalse EFalse  = True
eqConst EZero EZero  = True
eqConst ESucc ESucc  = True
eqConst EPred EPred  = True
eqConst EIsZero EIsZero  = True
eqConst _ _ = False

instance
  iEqConst : Eq Const
  iEqConst ._==_ = eqConst

{- Expr -}
eqExpr : Expr → Expr → Bool
eqExpr (EConst x) (EConst y) = eqConst x y
eqExpr (EIf e e₁ e₂) (EIf f f₁ f₂) = eqExpr e f && eqExpr e₁ f₁ && eqExpr e₂ f₂
eqExpr (EVar x) (EVar y) = x == y
eqExpr (ELam x t e) (ELam y s f) = x == y && eqType t s && eqExpr e f
eqExpr (EApp e e₁) (EApp f f₁) = eqExpr e f && eqExpr e₁ f₁
eqExpr _ _ = False

instance
  iEqExpr : Eq Expr
  iEqExpr ._==_ = eqExpr

{- Ctx -}

{- Val -}
eqVal : Val → Val → Bool
eqVal (VInt i) (VInt j) = i == j
eqVal (VBool a) (VBool b) = a == b
eqVal (VFun e) (VFun f) = e == f
eqVal _ _ = False

instance
  iEqVal : Eq Val
  iEqVal ._==_ = eqVal

------------------------------------------------------------
-- TYPE OF                                                --
------------------------------------------------------------

typeOfConst : Const → Type
typeOfConst ETrue = TBool
typeOfConst EFalse = TBool
typeOfConst EZero = TInt
typeOfConst ESucc = TFun TInt TInt
typeOfConst EPred = TFun TInt TInt
typeOfConst EIsZero = TFun TInt TBool

typeOf : Expr → Ctx Type → Maybe Type
typeOf (EConst c) _      = Just (typeOfConst c)
typeOf (EVar x) c        = findInCtx x c
typeOf (EIf iff thn els) c = 
    case typeOf iff c of λ where
        (Just TBool) → case (typeOf thn c , typeOf els c) of λ where
            (Just t , Just s) → if t == s then Just t else Nothing
            _ → Nothing
        _ → Nothing
typeOf (ELam x t e) c    = typeOf e (CCons x t c)
typeOf (EApp lam arg) c  =
    case (typeOf lam c , typeOf arg c) of λ where
        (Just (TFun i o) , Just a ) → if i == a then Just o else Nothing
        _ → Nothing

{-# COMPILE AGDA2HS typeOfConst #-}
{-# COMPILE AGDA2HS typeOf #-}

------------------------------------------------------------
-- INTERP                                                 --
------------------------------------------------------------

interpConst : Const → Val
interpLam : Expr → Val → Ctx Val → Maybe Val
interp : Expr → Ctx Val → Maybe Val


interpConst ETrue = VBool True
interpConst EFalse = VBool False
interpConst EZero = VInt 0
interpConst ESucc = VFun (EConst ESucc)
interpConst EPred = VFun (EConst EPred)
interpConst EIsZero = VFun (EConst EIsZero)

interpLam (EConst ESucc) (VInt i) nv = Just (VInt (i + 1))
interpLam (EConst EPred) (VInt i) nv = Just (VInt (i - 1))
interpLam (EConst EIsZero) (VInt i) nv = Just (VBool (i == 0))
interpLam (ELam x _ body) arg nv = interp body (CCons x arg nv)
interpLam _ _ _ = Nothing

interp (EConst c) nv = Just (interpConst c)
interp (EIf iff thn els) nv =
    case interp iff nv of λ where
        (Just (VBool True)) → interp thn nv
        (Just (VBool False)) → interp els nv
        _ → Nothing
interp (EVar x) nv = findInCtx x nv
interp lam@(ELam _ _ _) nv = Just (VFun lam)
interp (EApp (ELam x _ body) arg) nv =
    case interp arg nv of λ where
        (Just v) → interp body (CCons x v nv)
        _ → Nothing
interp (EApp lam arg) nv =
    case (interp lam nv , interp arg nv) of λ where
        (Just (VFun f) , Just v) → interpLam f v nv
        _ → Nothing


    -- case (interp lam nv , interp arg nv) of λ where
    --     (Just (VFun (EConst ESucc)) , Just (VInt i)) → Just (VInt (i + 3))
    --     (Just (VFun (EConst EPred)) , Just (VInt i)) → Just (VInt (i - 1))
    --     (Just (VFun (EConst EIsZero)) , Just (VInt i)) → Just (VBool (i == 0))
    --     -- (Just (VFun (ELam x _ body)) , Just v) → interp body (CCons x v nv) ⇒ ma boi causes a termination error
    --     _ → Nothing
