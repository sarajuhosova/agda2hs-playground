module TypeChecker.Intrinsic where

open import Haskell.Prelude

------------------------------------------------------------
-- TYPES                                                  --
------------------------------------------------------------

data Type : Set where
    TBool : Type
    TInt : Type

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

{-# COMPILE AGDA2HS Expr #-}

------------------------------------------------------------
-- TYPED EXPRESSIONS                                      --
------------------------------------------------------------

data TExpr : Type → Set where
    TEBool : Bool → TExpr TBool
    TEInt  : Int  → TExpr TInt
    TEAdd  : TExpr TInt → TExpr TInt → TExpr TInt
    TEEq   : TExpr TInt → TExpr TInt → TExpr TBool
    TENot  : TExpr TBool → TExpr TBool
    TEAnd  : TExpr TBool → TExpr TBool → TExpr TBool
    TEOr   : TExpr TBool → TExpr TBool → TExpr TBool

{-# COMPILE AGDA2HS TExpr #-}

------------------------------------------------------------
-- VALUES                                                 --
------------------------------------------------------------

data Val : Type → Set where
    VBool : Bool → Val TBool
    VInt  : Int  → Val TInt

{-# COMPILE AGDA2HS Val #-}

------------------------------------------------------------
-- TYPE PREDICATES                                        --
------------------------------------------------------------

data HasType : Expr → Type → Set where
    TBool : ∀ {b} → HasType (EBool b) TBool
    TInt  : ∀ {i} → HasType (EInt  i) TInt
    TAdd  : ∀ {left right}
        → HasType left TInt → HasType right TInt
        → HasType (EAdd left right) TInt
    TEq   : ∀ {left right}
        → HasType left TInt → HasType right TInt
        → HasType (EEq left right) TBool
    TNot  : ∀ {b}
        → HasType b TBool
        → HasType (ENot b) TBool
    TAnd  : ∀ {left right}
        → HasType left TBool → HasType right TBool
        → HasType (EAnd left right) TBool
    TOr   : ∀ {left right}
        → HasType left TBool → HasType right TBool
        → HasType (EOr left right) TBool

------------------------------------------------------------
-- DIRECT INTERPRETER                                     --
------------------------------------------------------------

interp : ∀ {e t} → Expr → HasType e t → Maybe (Val t)
interp (EBool b) TBool = Just (VBool b)
interp (EInt i) TInt = Just (VInt i)
interp (EAdd left right) (TAdd hl hr) =
    case (interp left hl , interp right hr) of λ where
        (Just (VInt l) , Just (VInt r)) → Just (VInt (l + r))
        _ → Nothing
interp (EEq left right) (TEq hl hr) =
    case (interp left hl , interp right hr) of λ where
        (Just (VInt l) , Just (VInt r)) → Just (VBool (l == r))
        _ → Nothing
interp (ENot e) (TNot h) =
    case (interp e h) of λ where
        (Just (VBool b)) → Just (VBool (not b))
        _ → Nothing
interp (EAnd left right) (TAnd hl hr) =
    case (interp left hl , interp right hr) of λ where
        (Just (VBool l) , Just (VBool r)) → Just (VBool (l && r))
        _ → Nothing
interp (EOr left right) (TOr hl hr) = 
    case (interp left hl , interp right hr) of λ where
        (Just (VBool l) , Just (VBool r)) → Just (VBool (l || r))
        _ → Nothing
interp _ _ = Nothing

------------------------------------------------------------
-- TYPE CHECKER                                           --
------------------------------------------------------------

typeOf : ∀ {e t} → Expr → HasType e t → Maybe (TExpr t)
typeOf (EBool b) TBool = Just (TEBool b)
typeOf (EInt i) TInt = Just (TEInt i)
typeOf (EAdd left right) (TAdd hl hr) = 
    case (typeOf left hl , typeOf right hr) of λ where
        (Just tLeft , Just tRight) → Just (TEAdd tLeft tRight)
        _ → Nothing
typeOf (EEq left right) (TEq hl hr) = 
    case (typeOf left hl , typeOf right hr) of λ where
        (Just tLeft , Just tRight) → Just (TEEq tLeft tRight)
        _ → Nothing
typeOf (ENot e) (TNot h) =
    case (typeOf e h) of λ where
        (Just tE) → Just (TENot tE)
        _ → Nothing
typeOf (EAnd left right) (TAnd hl hr) = 
    case (typeOf left hl , typeOf right hr) of λ where
        (Just tLeft , Just tRight) → Just (TEAnd tLeft tRight)
        _ → Nothing
typeOf (EOr left right) (TOr hl hr) = 
    case (typeOf left hl , typeOf right hr) of λ where
        (Just tLeft , Just tRight) → Just (TEOr tLeft tRight)
        _ → Nothing
typeOf _ _ = Nothing

------------------------------------------------------------
-- TYPED INTERPRETER                                      --
------------------------------------------------------------

safeInterp : ∀ {t} → TExpr t → Val t
safeInterp (TEBool b) = VBool b
safeInterp (TEInt i) = VInt i
safeInterp (TEAdd left right) =
    case (safeInterp left , safeInterp right) of λ where
        (VInt i , VInt j) → VInt (i + j)
safeInterp (TEEq left right) =
    case (safeInterp left , safeInterp right) of λ where
        (VInt i , VInt j) → VBool (i == j)
safeInterp (TENot e) =
    case (safeInterp e) of λ where
        (VBool b) → VBool (not b)
safeInterp (TEAnd left right) = 
    case (safeInterp left , safeInterp right) of λ where
        (VBool a , VBool b) → VBool (a && b)
safeInterp (TEOr left right) = 
    case (safeInterp left , safeInterp right) of λ where
        (VBool a , VBool b) → VBool (a || b)
