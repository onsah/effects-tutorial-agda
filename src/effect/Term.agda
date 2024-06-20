-- {-# OPTIONS --allow-unsolved-metas #-} 

open import Agda.Builtin.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst)
open import Data.Product using (Σ-syntax; ∃-syntax; _×_) renaming (_,′_ to ⟨_,_⟩)
open import Relation.Nullary.Decidable using (True)

open import effect.Util
open import effect.Type
open import effect.Context

module effect.Term where

    infix 3 _⨟_⊢v_
    infix 3 _⨟_⊢c_
    infix 5 _`·_
    infixl 5 _∷_
    infix 10 [_,_]↦_

    -- Thought it's appropriate to have effect context as a parameterized type since it's not supposed to change.
    -- Term typing rules are mutually recursive
    -- Can use '⨟' as separater between context
    data _⨟_⊢v_ (Σ : OpContext) (Γ : Context) : ValueType → Set
    -- Hmm: Maybe we should also have OpContext
    data _⨟_⊢c_ (Σ : OpContext) (Γ : Context) : ComputationType → Set

    data OpClause   (Σ : OpContext) (Γ : Context)
                    (Aᵢ Bᵢ B : ValueType)
                    (Δ : OpLabels)
                  : Set where
      [_,_]↦_  : {label : String}
              → (op : Operation label Aᵢ Bᵢ)
              → (Σ ∋ₑ op)
              → Σ ⨟ Γ ∷ Aᵢ ∷ (Bᵢ —→ B ! Δ) ⊢c B ! Δ
              → OpClause Σ Γ Aᵢ Bᵢ B Δ

    data OpClauses  (Σ : OpContext) (Γ : Context) 
                    (B : ValueType)
                    (Δ : OpLabels) 
                  : Set where
      ∅       : OpClauses Σ Γ B Δ
      _∷_     : {Aᵢ Bᵢ : ValueType}
              → OpClauses Σ Γ B Δ
              → OpClause Σ Γ Aᵢ Bᵢ B Δ
              → OpClauses Σ Γ B Δ
    
    opLabels  : {Σ : OpContext} {Γ : Context}
                {B : ValueType} {Δ : OpLabels}
              → OpClauses Σ Γ B Δ 
              → OpLabels
    opLabels  ∅ = ∅
    opLabels (Y ∷ [ label ⦂ _ —→ _ , _ ]↦ _) = (opLabels Y) ∷ label

    -- Asserts that every effect handler body is well typed according to it's effect
    record Handler  (Σ : OpContext) (Γ : Context) 
                    (A B : ValueType) (Δ : OpLabels) : Set 
      where
      inductive
      constructor handler[_,_]
      field
        return  : Σ ⨟ Γ ∷ A ⊢c B ! Δ
        ops : OpClauses Σ Γ B Δ

    -- Value terms
    data _⨟_⊢v_ Σ Γ where

        `_ : {A : ValueType}
           → Γ ∋ A
           → Σ ⨟ Γ ⊢v A
        
        `true : Σ ⨟ Γ ⊢v bool

        `false : Σ ⨟ Γ ⊢v bool
          
        `unit : Σ ⨟ Γ ⊢v unit

        `s  : String
            → Σ ⨟ Γ ⊢v str

        `fun : {A B : ValueType} {Δ : OpLabels}
             → Σ ⨟ (Γ ∷ A) ⊢c B ! Δ
             → Σ ⨟ Γ ⊢v A —→ B ! Δ

        `handler  : {Δ Δ' : OpLabels}
                    {A B : ValueType}
                  → (handlers : Handler Σ Γ A B Δ')
                  → (Δ \' (opLabels (Handler.ops handlers))) ⊆ Δ'
                  → Σ ⨟ Γ ⊢v A ! Δ ⟹ B ! Δ'

    data _⨟_⊢c_ Σ Γ where
        
        `return : {A : ValueType} {Δ : OpLabels}
                → Σ ⨟ Γ ⊢v A
                → Σ ⨟ Γ ⊢c A ! Δ

        -- Op rule
        `perform  : {Δ : OpLabels} 
                    {A Aₒₚ Bₒₚ : ValueType}
                    {opLabel : String} 
                  → (op : Operation opLabel Aₒₚ Bₒₚ)
                  → (∋?opLabel : True (Δ ∋-oL? opLabel))
                  → (∋?op : True (Σ ∋ₑ? op))
                  → (⊢arg : Σ ⨟ Γ ⊢v Aₒₚ)
                  → (⊢body : Σ ⨟ Γ ∷ Bₒₚ ⊢c A ! Δ)
                  → Σ ⨟ Γ ⊢c A ! Δ

        `do←—_`in_  : {Δ : OpLabels} 
                      {A B : ValueType}
                    → (⊢exp : Σ ⨟ Γ ⊢c A ! Δ)
                    → (⊢body : Σ ⨟ Γ ∷ A ⊢c B ! Δ)
                    → Σ ⨟ Γ ⊢c B ! Δ

        _`·_ : {A : ValueType} {Aₑ : ComputationType}
             → Σ ⨟ Γ ⊢v A —→ Aₑ
             → Σ ⨟ Γ ⊢v A
             → Σ ⨟ Γ ⊢c Aₑ

        `if_then_else : {Aₑ : ComputationType}
                      → Σ ⨟ Γ ⊢v bool
                      → Σ ⨟ Γ ⊢c Aₑ
                      → Σ ⨟ Γ ⊢c Aₑ
                      → Σ ⨟ Γ ⊢c Aₑ

        `with_handle_ : {Δ Δ' : OpLabels}
                        {A B : ValueType}
                      → Σ ⨟ Γ ⊢v A ! Δ' ⟹ B ! Δ
                      → Σ ⨟ Γ ⊢c A ! Δ' 
                      → Σ ⨟ Γ ⊢c B ! Δ
  