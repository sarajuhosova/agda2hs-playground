module TypeChecker.Safe where

open import Haskell.Prelude
open import TypeChecker.Lang

open import Data.Product using (∃;∃-syntax) renaming (_,_ to ⟨_,_⟩)

------------------------------------------------------------
-- EQUALITY                                               --
------------------------------------------------------------

data Same : Type → Type → Set where
    Yes : ∀ {t s}
        → (t == s) ≡ True
        → Same t s

------------------------------------------------------------
-- CONTEXT                                                --
------------------------------------------------------------

data In : Type → TCtx → Set where
    Z : ∀ {t ctx} → In t (t ∷ ctx)
    S : ∀ {t s ctx} → In t ctx → In t (s ∷ ctx)
    
isIn : (t : Type) → (ctx : TCtx) → Maybe (In t ctx)
isIn _ [] = Nothing
isIn t (x ∷ ctx) =
    case (t == x) of λ where
        True → Just {!   !}
        False → Nothing

-- eqIn : ∀ {t ctx} → In t ctx → In t ctx → Bool
-- eqIn Z Z = True
-- eqIn (S left) (S right) = eqIn left right
-- eqIn _ _ = False

-- instance
--   iEqIn : ∀ {@0 t ctx} → Eq (In t (t ∷ ctx))
--   iEqIn ._==_ = eqIn

------------------------------------------------------------
-- TYPED EXPRESSIONS                                      --
------------------------------------------------------------

data TExpr (ctx : TCtx) : @0 Type → Set where
    TEBool : Bool → TExpr ctx TBool
    TEInt  : Int  → TExpr ctx TInt
    TEAdd  : TExpr ctx TInt → TExpr ctx TInt → TExpr ctx TInt
    TEEq   : TExpr ctx TInt → TExpr ctx TInt → TExpr ctx TBool
    TENot  : TExpr ctx TBool → TExpr ctx TBool
    TEAnd  : TExpr ctx TBool → TExpr ctx TBool → TExpr ctx TBool
    TEOr   : TExpr ctx TBool → TExpr ctx TBool → TExpr ctx TBool
    TEVar  : ∀ {t} → In t ctx → TExpr ctx t

eqTExpr : ∀ {@0 t ctx} → TExpr ctx t → TExpr ctx t → Bool
eqTExpr (TEBool a) (TEBool b) = a == b
eqTExpr (TEInt i) (TEInt j) = i == j
eqTExpr (TEAdd left₁ right₁) (TEAdd left₂ right₂) = eqTExpr left₁ left₂ && eqTExpr right₁ right₂
eqTExpr (TEEq left₁ right₁) (TEEq left₂ right₂) = eqTExpr left₁ left₂ && eqTExpr right₁ right₂
eqTExpr (TENot a) (TENot b) = eqTExpr a b
eqTExpr (TEAnd left₁ right₁) (TEAnd left₂ right₂) = eqTExpr left₁ left₂ && eqTExpr right₁ right₂
eqTExpr (TEOr left₁ right₁) (TEOr left₂ right₂) = eqTExpr left₁ left₂ && eqTExpr right₁ right₂
eqTExpr (TEVar _) (TEVar _) = True
eqTExpr _ _ = False

instance
  iEqTExpr : ∀ {@0 t ctx} → Eq (TExpr ctx t)
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

simplify : ∀ {@0 t} → TVal t → Val
simplify (VBool b) = VBool b
simplify (VInt i) = VInt i

{-# COMPILE AGDA2HS simplify #-}

-- val : Type → Set
-- val TBool = Bool
-- val TInt = Int

Env : TCtx  → Set
Env C = All (λ t → TVal t) C

------------------------------------------------------------
-- TYPING JUDGEMENT                                       --
------------------------------------------------------------

data HasType (ctx : TCtx) : Expr → Type → Set where
    TBool : ∀ {b} → HasType ctx (EBool b) TBool
    TInt  : ∀ {i} → HasType ctx (EInt  i) TInt
    TAdd  : ∀ {left right}
        → HasType ctx left TInt → HasType ctx right TInt
        → HasType ctx (EAdd left right) TInt
    TEq   : ∀ {left right}
        → HasType ctx left TInt → HasType ctx right TInt
        → HasType ctx (EEq left right) TBool
    TNot  : ∀ {e}
        → HasType ctx e TBool
        → HasType ctx (ENot e) TBool
    TAnd  : ∀ {left right}
        → HasType ctx left TBool → HasType ctx right TBool
        → HasType ctx (EAnd left right) TBool
    TOr   : ∀ {left right}
        → HasType ctx left TBool → HasType ctx right TBool
        → HasType ctx (EOr left right) TBool
    TVar  : ∀ {x t}
        → In t ctx
        → HasType ctx (EVar x) t
        
------------------------------------------------------------
-- TYPE CHECK                                             --
------------------------------------------------------------

-- record Σ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
--   constructor _,_
--   field
--     fst : A
--     snd : B fst

-- record TypeProof {e : Expr} {t : Type} (T : Set t) (P : T → HasType e T) : Set where
--     field
--         type : T
--         proof : P type

typeProof' : (e : Expr) → (ctx : TCtx) → Maybe (∃[ t ](HasType ctx e t))
typeProof' (EBool _) ctx = Just ⟨ TBool , TBool ⟩
typeProof' (EInt _) ctx = Just ⟨ TInt , TInt ⟩
typeProof' (EAdd left right) ctx =
    case (typeProof' left ctx , typeProof' right ctx) of λ where
        (Just ⟨ TInt , hₗ ⟩ , Just ⟨ TInt , hᵣ ⟩)
            → Just ⟨ TInt , TAdd hₗ hᵣ ⟩
        _   → Nothing
typeProof' (EEq left right) ctx = 
    case (typeProof' left ctx , typeProof' right ctx) of λ where
        (Just ⟨ TInt , hₗ ⟩ , Just ⟨ TInt , hᵣ ⟩)
            → Just ⟨ TBool , TEq hₗ hᵣ ⟩
        _   → Nothing
typeProof' (ENot e) ctx =
    case (typeProof' e ctx) of λ where
        (Just ⟨ TBool , h ⟩)
            → Just ⟨ TBool , TNot h ⟩
        _   → Nothing
typeProof' (EAnd left right) ctx = 
    case (typeProof' left ctx , typeProof' right ctx) of λ where
        (Just ⟨ TBool , hₗ ⟩ , Just ⟨ TBool , hᵣ ⟩)
            → Just ⟨ TBool , TAnd hₗ hᵣ ⟩
        _   → Nothing
typeProof' (EOr left right) ctx =
    case (typeProof' left ctx , typeProof' right ctx) of λ where
        (Just ⟨ TBool , hₗ ⟩ , Just ⟨ TBool , hᵣ ⟩)
            → Just ⟨ TBool , TOr hₗ hᵣ ⟩
        _   → Nothing
typeProof' (EVar x) ctx =
    case (get x ctx) of λ where
        (Just t) → Just ⟨ t , TVar {!   !} ⟩
        _ → Nothing

typeProof : (e : Expr) → Maybe (∃[ t ](HasType [] e t))
typeProof e = typeProof' e []

{-# COMPILE AGDA2HS typeProof' #-}
        
------------------------------------------------------------
-- TYPED INTERPRETER                                      --
------------------------------------------------------------

convert : ∀ {@0 t ctx} → (e : Expr) → @0 HasType ctx e t → TExpr ctx t
convert (EBool b) TBool = TEBool b
convert (EInt i) TInt = TEInt i
convert (EAdd left right) (TAdd hl hr) = TEAdd (convert left hl) (convert right hr)
convert (EEq left right) (TEq hl hr) = TEEq (convert left hl) (convert right hr)
convert (ENot e) (TNot h) = TENot (convert e h)
convert (EAnd left right) (TAnd hl hr) = TEAnd (convert left hl) (convert right hr)
convert (EOr left right) (TOr hl hr) = TEOr (convert left hl) (convert right hr)
convert (EVar x) (TVar hx) = {!   !}

typedInterp : ∀ {@0 t ctx} → TExpr ctx t → TVal t
typedInterp (TEBool b) = VBool b
typedInterp (TEInt i) = VInt i
typedInterp (TEAdd left right) =
    case (typedInterp left , typedInterp right) of λ where
        (VInt i , VInt j) → VInt (i + j)
typedInterp (TEEq left right) =
    case (typedInterp left , typedInterp right) of λ where
        (VInt i , VInt j) → VBool (i == j)
typedInterp (TENot e) =
    case (typedInterp e) of λ where
        (VBool b) → VBool (not b)
typedInterp (TEAnd left right) = 
    case (typedInterp left , typedInterp right) of λ where
        (VBool a , VBool b) → VBool (a && b)
typedInterp (TEOr left right) = 
    case (typedInterp left , typedInterp right) of λ where
        (VBool a , VBool b) → VBool (a || b)
typedInterp (TEVar x) = {!   !}

{-# COMPILE AGDA2HS convert #-}
{-# COMPILE AGDA2HS typedInterp #-}
        
------------------------------------------------------------
-- SAFE INTERP                                            --
------------------------------------------------------------

-- combine' : Expr → Maybe (∃[ t ](TVal t))
-- combine' e with typeProof' e
-- ... | Just ⟨ t , h ⟩ = Just ⟨ t , typedInterp (convert e h) ⟩
-- ... | _              = Nothing

-- safeInterp' : Expr → Maybe Val
-- safeInterp' e with combine' e
-- ... | Just ⟨ _ , v ⟩ = Just (simplify v)
-- ... | _ = Nothing

safeInterp : Expr → Maybe Val
safeInterp e =
    case (typeProof e) of λ where
        (Just ⟨ t , h ⟩) 
            → Just (simplify (typedInterp (convert e h)))
        _   → Nothing

{-# COMPILE AGDA2HS safeInterp #-}

------------------------------------------------------------
-- PROOFS                                                 --
------------------------------------------------------------

_ : HasType [] (EAdd (EInt 3) (EInt 5)) TInt
_ = TAdd TInt TInt
 