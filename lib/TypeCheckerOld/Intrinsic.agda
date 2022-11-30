{-# OPTIONS --allow-unsolved-metas #-}

module TypeCheckerOld.Intrinsic where

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

eqExpr : Expr → Expr → Bool
eqExpr (EBool a) (EBool b) = a == b
eqExpr (EInt i) (EInt j) = i == j
eqExpr (EAdd left₁ right₁) (EAdd left₂ right₂) = eqExpr left₁ left₂ && eqExpr right₁ right₂
eqExpr (EEq left₁ right₁) (EEq left₂ right₂) = eqExpr left₁ left₂ && eqExpr right₁ right₂
eqExpr (ENot a) (ENot b) = eqExpr a b
eqExpr (EAnd left₁ right₁) (EAnd left₂ right₂) = eqExpr left₁ left₂ && eqExpr right₁ right₂
eqExpr (EOr left₁ right₁) (EOr left₂ right₂) = eqExpr left₁ left₂ && eqExpr right₁ right₂
eqExpr _ _ = False

instance
  iEqExpr : Eq Expr
  iEqExpr ._==_ = eqExpr

{-# COMPILE AGDA2HS Expr #-}

------------------------------------------------------------
-- TYPED EXPRESSIONS                                      --
------------------------------------------------------------

data TExpr : @0 Type → Set where
    TEBool : Bool → TExpr TBool
    TEInt  : Int  → TExpr TInt
    TEAdd  : TExpr TInt → TExpr TInt → TExpr TInt
    TEEq   : TExpr TInt → TExpr TInt → TExpr TBool
    TENot  : TExpr TBool → TExpr TBool
    TEAnd  : TExpr TBool → TExpr TBool → TExpr TBool
    TEOr   : TExpr TBool → TExpr TBool → TExpr TBool

eqTExpr : ∀ {t} → TExpr t → TExpr t → Bool
eqTExpr (TEBool a) (TEBool b) = a == b
eqTExpr (TEInt i) (TEInt j) = i == j
eqTExpr (TEAdd left₁ right₁) (TEAdd left₂ right₂) = eqTExpr left₁ left₂ && eqTExpr right₁ right₂
eqTExpr (TEEq left₁ right₁) (TEEq left₂ right₂) = eqTExpr left₁ left₂ && eqTExpr right₁ right₂
eqTExpr (TENot a) (TENot b) = eqTExpr a b
eqTExpr (TEAnd left₁ right₁) (TEAnd left₂ right₂) = eqTExpr left₁ left₂ && eqTExpr right₁ right₂
eqTExpr (TEOr left₁ right₁) (TEOr left₂ right₂) = eqTExpr left₁ left₂ && eqTExpr right₁ right₂
eqTExpr _ _ = False

instance
  iEqTExpr : ∀ {t} → Eq (TExpr t)
  iEqTExpr ._==_ = eqTExpr

{-# COMPILE AGDA2HS TExpr #-}

------------------------------------------------------------
-- VALUES                                                 --
------------------------------------------------------------

data Val : @0 Type → Set where
    VBool : Bool → Val TBool
    VInt  : Int  → Val TInt

eqVal : ∀ {t} → Val t → Val t → Bool
eqVal (VBool a) (VBool b) = a == b
eqVal (VInt i) (VInt j) = i == j

instance
  iEqVal : ∀ {t} → Eq (Val t)
  iEqVal ._==_ = eqVal

{-# COMPILE AGDA2HS Val #-}

val : Type → Set
val TBool = Bool
val TInt = Int

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

interp' : ∀ {@0 t} → Expr → Maybe (Val t)
interp' = {!   !}

interp : ∀ {@0 t} → (e : Expr) → HasType e t → Maybe (Val t)
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

{-# COMPILE AGDA2HS interp #-}

------------------------------------------------------------
-- TYPE CHECKER                                           --
------------------------------------------------------------

-- typeOf' : Expr → sigma t + proof
-- typeOf' e = {!   !}

convert : ∀ {@0 t} → (e : Expr) → HasType e t → TExpr t
convert (EBool b) TBool = TEBool b
convert (EInt i) TInt = TEInt i
convert (EAdd left right) (TAdd hl hr) = TEAdd (convert left hl) (convert right hr)
convert (EEq left right) (TEq hl hr) = TEEq (convert left hl) (convert right hr)
convert (ENot e) (TNot h) = TENot (convert e h)
convert (EAnd left right) (TAnd hl hr) = TEAnd (convert left hl) (convert right hr)
convert (EOr left right) (TOr hl hr) = TEOr (convert left hl) (convert right hr)

-- {-# COMPILE AGDA2HS typeOf #-}

------------------------------------------------------------
-- TYPED INTERPRETER                                      --
------------------------------------------------------------

safeInterp : ∀ {@0 t} → TExpr t → Val t
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

{-# COMPILE AGDA2HS safeInterp #-}

------------------------------------------------------------
-- PROOFS                                                 --
------------------------------------------------------------

_ : HasType (EAdd (EInt 3) (EInt 5)) TInt
_ = TAdd TInt TInt

