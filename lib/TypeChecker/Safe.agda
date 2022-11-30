module TypeChecker.Safe where

open import Haskell.Prelude
open import TypeChecker.Lang

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
-- VALUES                                                 --
------------------------------------------------------------

val : Type → Set
val TBool = Bool
val TInt = Int
