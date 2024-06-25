
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
    infix 4 `do←—_`in_
    infix 5 _`·_
    infixl 5 _∷_
    infix 10 [_,_]↦_

    data _⨟_⊢v_ (Σ : OpContext) (Γ : Context) : ValueType → Set
    data _⨟_⊢c_ (Σ : OpContext) (Γ : Context) : ComputationType → Set

    -- An OpClause is an operation and a term that will be used when this operation is performed.
    data OpClause   (Σ : OpContext) (Γ : Context)
                    (Aᵢ Bᵢ B : ValueType)
                    (Δ : OpContext)
                    (label : String)
                  : Set where
      [_,_]↦_ : (op : Operation label Aᵢ Bᵢ)
              → (Σ ∋-op op)
              → Σ ⨟ Γ ∷ Aᵢ ∷ (Bᵢ —→ B ! Δ) ⊢c B ! Δ
              → OpClause Σ Γ Aᵢ Bᵢ B Δ label

    data OpClauses  (Σ : OpContext) (Γ : Context) 
                    (B : ValueType)
                    (Δ : OpContext) 
                  : Set where
      ∅       : OpClauses Σ Γ B Δ
      _∷_     : {Aᵢ Bᵢ : ValueType} {label : String}
              → OpClauses Σ Γ B Δ
              → OpClause Σ Γ Aᵢ Bᵢ B Δ label
              → OpClauses Σ Γ B Δ
    
    opContext  : {Σ : OpContext} {Γ : Context}
                {B : ValueType} {Δ : OpContext}
              → OpClauses Σ Γ B Δ 
              → OpContext
    opContext  ∅ = ∅
    opContext (Y ∷ [ op , _ ]↦ _) = (opContext Y) ∷ op

    -- A handler block that contains:
    -- `return`: Default clause when the computation returns normally.
    -- `ops`: Clauses for operations when compputation performs an effect.
    record Handler  (Σ : OpContext) (Γ : Context) 
                    (A B : ValueType) (Δ : OpContext) : Set 
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

        `fun : {A B : ValueType} {Δ : OpContext}
             → Σ ⨟ (Γ ∷ A) ⊢c B ! Δ
             → Σ ⨟ Γ ⊢v A —→ B ! Δ

        `handler  : {Δ Δ' : OpContext}
                    {A B : ValueType}
                  → (handlers : Handler Σ Γ A B Δ')
                  → (Δ \' (opContext (Handler.ops handlers))) ⊆ Δ'
                  → Σ ⨟ Γ ⊢v A ! Δ ⟹ B ! Δ'

    -- Computation terms
    data _⨟_⊢c_ Σ Γ where
        
        `return : {A : ValueType} {Δ : OpContext}
                → Σ ⨟ Γ ⊢v A
                → Σ ⨟ Γ ⊢c A ! Δ

        `perform  : {Δ : OpContext} 
                    {A Aₒₚ Bₒₚ : ValueType}
                    {opLabel : String} 
                  → (op : Operation opLabel Aₒₚ Bₒₚ)
                  → (Σ∋op : Σ ∋-op op)
                  → (Δ∋op : Δ ∋-op op)
                  → (⊢arg : Σ ⨟ Γ ⊢v Aₒₚ)
                  → (⊢body : Σ ⨟ Γ ∷ Bₒₚ ⊢c A ! Δ)
                  → Σ ⨟ Γ ⊢c A ! Δ

        `do←—_`in_  : {Δ : OpContext} 
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

        `with_handle_ : {Δ Δ' : OpContext}
                        {A B : ValueType}
                      → Σ ⨟ Γ ⊢v A ! Δ' ⟹ B ! Δ
                      → Σ ⨟ Γ ⊢c A ! Δ' 
                      → Σ ⨟ Γ ⊢c B ! Δ
   