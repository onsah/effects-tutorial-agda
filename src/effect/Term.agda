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

    -- Thought it's appropriate to have effect context as a parameterized type since it's not supposed to change.
    -- Term typing rules are mutually recursive
    -- Can use '⨟' as separater between context
    data _⨟_⊢v_ (Σ : OpContext) (Γ : Context) : ValueType → Set
    -- Hmm: Maybe we should also have OpContext
    data _⨟_⊢c_ (Σ : OpContext) (Γ : Context) : ComputationType → Set

    OpHandler : (Σ : OpContext) (Γ : Context)
              → (Aᵢ : ValueType)
              → (Bᵢ : ValueType)
              → (B : ValueType)
              → (Δ : OpLabels)
              → Set
    OpHandler  Σ Γ Aᵢ Bᵢ B Δ = Σ ⨟ Γ , Aᵢ , (Bᵢ —→ B ! Δ) ⊢c B ! Δ 

    data OpHandlers (Σ : OpContext) (Γ : Context) 
                        (B : ValueType)
                        (Δ : OpLabels) : Set 
      where
      ∅       : OpHandlers Σ Γ B Δ
      -- TODO: drop brackets
      _∷[_,_⇒_] : {label : String} {Aᵢ Bᵢ : ValueType}
              → OpHandlers Σ Γ B Δ
              → (op : Operation label Aᵢ Bᵢ)
              → (Σ ∋ₑ op)
              → OpHandler Σ Γ Aᵢ Bᵢ B Δ
              → OpHandlers Σ Γ B Δ
    
    opLabels  : {Σ : OpContext} {Γ : Context}
                {B : ValueType} {Δ : OpLabels}
              → OpHandlers Σ Γ B Δ 
              → OpLabels
    opLabels  ∅ = ∅
    opLabels  (_∷[_,_⇒_] {label = label} Υ _ _ _) = (opLabels Υ) , label

    -- Asserts that every effect handler body is well typed according to it's effect
    record Handler  (Σ : OpContext) (Γ : Context) 
                    (A B : ValueType) (Δ : OpLabels) : Set 
      where
      inductive
      field
        return  : Σ ⨟ Γ , A ⊢c B ! Δ
        ops : OpHandlers Σ Γ B Δ

      -- TODO: create a constructor
      -- constructor ∥[return_,_] 

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
             → Σ ⨟ (Γ , A) ⊢c B ! Δ
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
                  → (⊢body : Σ ⨟ Γ , Bₒₚ ⊢c A ! Δ)
                  → Σ ⨟ Γ ⊢c A ! Δ

        `do←—_`in_  : {Δ : OpLabels} 
                      {A B : ValueType}
                    → (⊢exp : Σ ⨟ Γ ⊢c A ! Δ)
                    → (⊢body : Σ ⨟ Γ , A ⊢c B ! Δ)
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
  