module TypeChecker.Safe where

open import Haskell.Prelude
open import TypeChecker.Lang

open import Data.Product using (∃;∃-syntax)
open import Relation.Nullary using (Dec;yes;no)

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

eqTExpr : ∀ {@0 t} → TExpr t → TExpr t → Bool
eqTExpr (TEBool a) (TEBool b) = a == b
eqTExpr (TEInt i) (TEInt j) = i == j
eqTExpr (TEAdd left₁ right₁) (TEAdd left₂ right₂) = eqTExpr left₁ left₂ && eqTExpr right₁ right₂
eqTExpr (TEEq left₁ right₁) (TEEq left₂ right₂) = eqTExpr left₁ left₂ && eqTExpr right₁ right₂
eqTExpr (TENot a) (TENot b) = eqTExpr a b
eqTExpr (TEAnd left₁ right₁) (TEAnd left₂ right₂) = eqTExpr left₁ left₂ && eqTExpr right₁ right₂
eqTExpr (TEOr left₁ right₁) (TEOr left₂ right₂) = eqTExpr left₁ left₂ && eqTExpr right₁ right₂
eqTExpr _ _ = False

instance
  iEqTExpr : ∀ {@0 t} → Eq (TExpr t)
  iEqTExpr ._==_ = eqTExpr

{-# COMPILE AGDA2HS TExpr #-}

------------------------------------------------------------
-- VALUES                                                 --
------------------------------------------------------------

data TVal : @0 Type → Set where
    VBool : Bool → TVal TBool
    VInt  : Int  → TVal TInt

eqTVal : ∀ {@0 t} → TVal t → TVal t → Bool
eqTVal (VBool a) (VBool b) = a == b
eqTVal (VInt i) (VInt j) = i == j

instance
  iEqTVal : ∀ {@0 t} → Eq (TVal t)
  iEqTVal ._==_ = eqTVal

{-# COMPILE AGDA2HS TVal #-}

val : Type → Set
val TBool = Bool
val TInt = Int

------------------------------------------------------------
-- TYPING JUDGEMENT                                       --
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
    TNot  : ∀ {e}
        → HasType e TBool
        → HasType (ENot e) TBool
    TAnd  : ∀ {left right}
        → HasType left TBool → HasType right TBool
        → HasType (EAnd left right) TBool
    TOr   : ∀ {left right}
        → HasType left TBool → HasType right TBool
        → HasType (EOr left right) TBool
        
------------------------------------------------------------
-- TYPE CHECK                                             --
------------------------------------------------------------

type : (e : Expr) → Dec (∃[ t ](HasType e t))
type (EBool b) = yes {! !}
type (EInt i) = {!   !}
type (EAdd left right) = {!   !}
type (EEq left right) = {!   !}
type (ENot e) = {!   !}
type (EAnd left right) = {!   !}
type (EOr left right) = {!   !}
        
------------------------------------------------------------
-- SAFE INTERPRETER                                       --
------------------------------------------------------------

convert : ∀ {@0 t} → (e : Expr) → HasType e t → TExpr t
convert (EBool b) TBool = TEBool b
convert (EInt i) TInt = TEInt i
convert (EAdd left right) (TAdd hl hr) = TEAdd (convert left hl) (convert right hr)
convert (EEq left right) (TEq hl hr) = TEEq (convert left hl) (convert right hr)
convert (ENot e) (TNot h) = TENot (convert e h)
convert (EAnd left right) (TAnd hl hr) = TEAnd (convert left hl) (convert right hr)
convert (EOr left right) (TOr hl hr) = TEOr (convert left hl) (convert right hr)

safeInterp : ∀ {@0 t} → TExpr t → TVal t
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
