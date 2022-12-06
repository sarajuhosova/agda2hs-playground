module TypeChecker.Interp where

open import Haskell.Prelude
open import TypeChecker.Lang

import Relation.Binary.PropositionalEquality as PEq
open PEq using (_≡_; refl)
open PEq.≡-Reasoning using (begin_; _≡⟨⟩_;  _∎)

------------------------------------------------------------
-- DIRECT INTERPRETER                                     --
------------------------------------------------------------

interp' : Expr → VCtx → Maybe Val
interp' (EBool b) _ = Just (VBool b)
interp' (EInt i) _ = Just (VInt i)
interp' (EAdd left right) ctx =
    case (interp' left ctx , interp' right ctx) of λ where
        (Just (VInt i) , Just (VInt j)) → Just (VInt (i + j))
        _ → Nothing
interp' (EEq left right) ctx =
    case (interp' left ctx , interp' right ctx) of λ where
        (Just (VInt i) , Just (VInt j)) → Just (VBool (i == j))
        _ → Nothing
interp' (ENot e) ctx =
    case interp' e ctx of λ where
        (Just (VBool b)) → Just (VBool (not b))
        _ → Nothing
interp' (EAnd left right) ctx =
    case (interp' left ctx , interp' right ctx) of λ where
        (Just (VBool a) , Just (VBool b)) → Just (VBool (a && b))
        _ → Nothing
interp' (EOr left right) ctx =
    case (interp' left ctx , interp' right ctx) of λ where
        (Just (VBool a) , Just (VBool b)) → Just (VBool (a || b))
        _ → Nothing
interp' (EVar x) ctx = get x ctx

interp : Expr → Maybe Val
interp e = interp' e []

{-# COMPILE AGDA2HS interp' #-}
{-# COMPILE AGDA2HS interp #-}

------------------------------------------------------------
-- SIMPLE TYPE CHECKER                                    --
------------------------------------------------------------

typeOf' : Expr → TCtx → Maybe Type
typeOf' (EBool b) _ = Just TBool
typeOf' (EInt i) _ = Just TInt
typeOf' (EAdd left right) ctx =
    case (typeOf' left ctx , typeOf' right ctx) of λ where
        (Just TInt , Just TInt) → Just TInt
        _ → Nothing
typeOf' (EEq left right) ctx =
    case (typeOf' left ctx , typeOf' right ctx) of λ where
        (Just TInt , Just TInt) → Just TBool
        _ → Nothing
typeOf' (ENot e) ctx =
    case typeOf' e ctx of λ where
        (Just TBool) → Just TBool
        _ → Nothing
typeOf' (EAnd left right) ctx =
    case (typeOf' left ctx , typeOf' right ctx) of λ where
        (Just TBool , Just TBool) → Just TBool
        _ → Nothing
typeOf' (EOr left right) ctx =
    case (typeOf' left ctx , typeOf' right ctx) of λ where
        (Just TBool , Just TBool) → Just TBool
        _ → Nothing
typeOf' (EVar x) ctx = get x ctx

typeOf : Expr → Maybe Type
typeOf e = typeOf' e []

{-# COMPILE AGDA2HS typeOf' #-}
{-# COMPILE AGDA2HS typeOf #-}

------------------------------------------------------------
-- PROOFS                                                 --
------------------------------------------------------------

bogus : Maybe Val
bogus = interp (ENot (EInt 13))

_ : (bogus == Nothing) ≡ True
_ = refl

three : Maybe Val
three = Just (VInt 3)

three₁ : Maybe Val
three₁ = interp (EInt 3)

three₂ : Maybe Val
three₂ = interp (EAdd (EInt 1) (EAdd (EInt 1) (EInt 1)))

threeV : Maybe Val
threeV = interp' (EVar 2) ((VBool False) ∷ ((VInt 3) ∷ ((VInt 13) ∷ ((VBool True) ∷ []))))

_ : (three == three₁) ≡ True
_ = refl

_ : (three == three₂) ≡ True
_ = refl

_ : (three₁ == three₂) ≡ True
_ = refl

_ : (threeV == three) ≡ True
_ = refl

-- sound : ∀ {e} → ((typeOf' e) == Nothing) ≡ False → ((interp' e) == Nothing) ≡ False
-- sound h = {!   !}


