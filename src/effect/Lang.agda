
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Maybe using (Maybe)
open import Agda.Builtin.List using (List; _∷_; [])

module effect.Lang where

    infix 3 _⊢v_
    infix 3 _⊢c_
    infix  4 _∋_
    infixl 5 _,_
    infix 4 _!_
    infix 5 _—→_

    data ValueType : Set
    data ComputationType : Set
    data Effect : Set

    data ValueType where
        bool : ValueType
        str  : ValueType
        int  : ValueType
        unit : ValueType
        void : ValueType
        _—→_ : ValueType → ComputationType → ValueType
        _⟹_ : ComputationType → ComputationType → ValueType

    data ComputationType where
        -- Effect list is an overappromixation of what the computation actually uses.
        _!_ : ValueType → List Effect → ComputationType

    data Effect where
        _⦂_—→_ : String → ValueType → ValueType → Effect

    data Context : Set where
        ∅ : Context
        _,_ : Context → ValueType → Context

    data _∋_ : Context → ValueType → Set where
        Z : {Γ : Context} {A : ValueType}
          → Γ , A ∋ A    

    -- Term typing rules are mutually recursive
    data _⊢v_ : Context → ValueType → Set
    data _⊢c_ : Context → ComputationType → Set

    -- Value terms
    data _⊢v_ where

        `_ : {Γ : Context} {A : ValueType}
           → Γ ∋ A
           → Γ ⊢v A
        
        `true : {Γ : Context}
              → Γ ⊢v bool

        `false : {Γ : Context}
               → Γ ⊢v bool

        `fun : {Γ : Context} {A : ValueType} {Aₑ : ComputationType}
             → (Γ , A) ⊢c Aₑ
             → Γ ⊢v A —→ Aₑ

    data _⊢c_ where
        
        `return : {Γ : Context} {A : ValueType} {Δ : List Effect}
                → Γ ⊢v A
                → Γ ⊢c A ! Δ
        