
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Maybe using (Maybe)
open import Relation.Binary.PropositionalEquality using (_≡_)

module effect.Lang where

    infix 3 _>_⊢v_
    infix 3 _>_⊢c_
    infix  4 _∋_
    infix  4 _∋ₑ_
    infix  4 _∋ₑₗ_
    infixl 5 _,_
    infixl 5 _,ₑ_
    infixl 5 _,ₑₗ_
    infix 4 _!_
    infix 5 _—→_
    infix 5 _⟹_
    infix 5 _⦂_—→_

    data ValueType : Set
    data ComputationType : Set
    data Operation : String → ValueType → ValueType → Set

    data ValueType where
        bool : ValueType
        str  : ValueType
        int  : ValueType
        unit : ValueType
        void : ValueType
        _—→_ : ValueType → ComputationType → ValueType
        _⟹_ : ComputationType → ComputationType → ValueType

    data Operation where
        _⦂_—→_ : (label : String) → (A : ValueType) → (B : ValueType) → Operation label A B

    data Context : Set where
        ∅ : Context
        _,_ : Context → ValueType → Context

    data _∋_ : Context → ValueType → Set where
        Z : {Γ : Context} {A : ValueType}
          → Γ , A ∋ A
        
        S_ : {Γ : Context} {A B : ValueType}
           → Γ ∋ A
           → Γ , B ∋ A

    -- Unlike Context, this is fixed throughtout the whole program.
    -- It's the list of predefined effect signatures that could be used in the program.
    data OpContext : Set where
        ∅ₑ : OpContext
        _,ₑ_ : {label : String} {A B : ValueType}
             → OpContext → Operation label A B → OpContext

    data _∋ₑ_ : {label : String} {A B : ValueType}
              → OpContext → Operation label A B → Set 
        where
        Zₑ  : {Γ : OpContext} {label : String} {A B : ValueType} 
              {op : Operation label A B}
            → Γ ,ₑ op ∋ₑ op
        
        Sₑ_ : {Γ : OpContext} {label label' : String} {A A' B B' : ValueType} 
              {op : Operation label A B} {op' : Operation label' A' B'}
            → Γ ∋ₑ op
            → Γ ,ₑ op' ∋ₑ op

    data OpLabelContext : Set where
        ∅ₑₗ : OpLabelContext
        _,ₑₗ_ : OpLabelContext → String → OpLabelContext

    data _∋ₑₗ_ : OpLabelContext → String → Set where
        Zₑ : {Γ : OpLabelContext} {label : String}
          → Γ ,ₑₗ label ∋ₑₗ label
        
        Sₑ_ : {Γ : OpLabelContext} {label label' : String}
           → Γ ∋ₑₗ label
           → Γ ,ₑₗ label' ∋ₑₗ label

    data ComputationType where
        -- Operation list is an overappromixation of what the computation actually uses.
        _!_ : ValueType → OpLabelContext → ComputationType

    -- Thought it's appropriate to have effect context as a parameterized type since it's not supposed to change.
    -- Term typing rules are mutually recursive
    data _>_⊢v_ (Σ : OpContext) : Context → ValueType → Set
    -- Hmm: Maybe we should also have OpContext
    data _>_⊢c_ (Σ : OpContext) : Context → ComputationType → Set

    -- Value terms
    data _>_⊢v_ Σ where

        `_ : {Γ : Context} {A : ValueType}
           → Γ ∋ A
           → Σ > Γ ⊢v A
        
        `true : {Γ : Context}
              → Σ > Γ ⊢v bool

        `false : {Γ : Context}
               → Σ > Γ ⊢v bool

        `fun : {Γ : Context} {A : ValueType} {Aₑ : ComputationType}
             → Σ > (Γ , A) ⊢c Aₑ
             → Σ > Γ ⊢v A —→ Aₑ

    data _>_⊢c_ Σ where
        
        `return : {Γ : Context} {A : ValueType} {Δ : OpLabelContext}
                → Σ > Γ ⊢v A
                → Σ > Γ ⊢c A ! Δ

        -- Op rule
        `op_[_⨾_⇒_] : {Γ : Context} {Δ : OpLabelContext} 
                      {A Aₒₚ Bₒₚ : ValueType}
                      {opLabel : String} {op : Operation opLabel Aₒₚ Bₒₚ}
                    → Σ ∋ₑ op
                    → Σ > Γ ⊢v Aₒₚ
                    → Σ > Γ , Bₒₚ ⊢c A ! Δ
                    → Δ ∋ₑₗ opLabel
                    → Σ > Γ ⊢c A ! Δ

        `do_←—_`in_ : {Γ : Context} {Δ : OpLabelContext} 
                      {A B : ValueType}
                    → Σ > Γ ⊢c A ! Δ
                    → Σ > Γ , A ⊢c B ! Δ
                    → Σ > Γ ⊢c B ! Δ

        _`·_ : {Γ : Context}
               {A : ValueType} {Aₑ : ComputationType}
             → Σ > Γ ⊢v A —→ Aₑ
             → Σ > Γ ⊢v A
             → Σ > Γ ⊢c Aₑ

        `if_then_else : {Γ : Context}
                        {Aₑ : ComputationType}
                      → Σ > Γ ⊢v bool
                      → Σ > Γ ⊢c Aₑ
                      → Σ > Γ ⊢c Aₑ
                      → Σ > Γ ⊢c Aₑ

        `with_handle_ : {Γ : Context}
                        {Aₑ Bₑ : ComputationType}
                      → Σ > Γ ⊢v Aₑ ⟹ Bₑ
                      → Σ > Γ ⊢c Aₑ
                      → Σ > Γ ⊢c Bₑ