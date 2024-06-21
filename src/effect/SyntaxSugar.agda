
open import Data.String using (String)
open import Relation.Nullary.Decidable using (True; toWitness)
open import Data.Nat using (ℕ)

open import effect.Type
open import effect.Context
open import effect.Term
open import effect.Renaming

module effect.SyntaxSugar where

    infixr  3 _⨟_

    opCall[_] : {A B : ValueType}
                {Σ : OpContext} {Γ : Context} 
                {Δ : OpContext} {opLabel : String}
              → (op : Operation opLabel A B)
              → {True (Σ ∋-op? op)}
              → {True (Δ ∋-op? op)}
              → Σ ⨟ Γ ⊢v A —→ B ! Δ
    opCall[_] op {Σ∋?op} {Δ∋?op} =
      `fun (`perform op (toWitness Σ∋?op) (toWitness Δ∋?op) (` Z) (`return (` Z)))

    open import Data.Nat using (_<_; _≤?_; zero; suc; s≤s)
    open import Relation.Nullary.Decidable using (toWitness)

    private
      length  : Context → ℕ
      length ∅ = zero
      length (Γ ∷ _) = suc (length Γ)

      lookup  : {Γ : Context} → {n : ℕ}
              → (p : n < length Γ)
              → ValueType
      lookup {Γ = _ ∷ A} {n = zero} _ = A
      lookup {Γ = _ ∷ _} {n = suc _} (s≤s p) = (lookup p)

      count   : {Γ : Context} → {n : ℕ}
              → (p : n < length Γ)
              → Γ ∋ lookup p
      count {Γ = _ ∷ _} {n = zero } _ = Z
      count {Γ = _ ∷ _} {n = suc _} (s≤s p) = S (count p)

    
    #_  : {Γ : Context} {Σ : OpContext}
        → (n : ℕ)
        → {n∈Γ : True (suc n ≤? length Γ)}
          --------------------------------
        → Σ ⨟ Γ ⊢v lookup (toWitness n∈Γ)
    #_  _ {n∈Γ = n∈Γ}  = ` (count (toWitness n∈Γ))

    -- Sequencing
    _⨟_ : {Γ : Context} {Σ : OpContext}
          {A B : ValueType} {Δ : OpContext}
        → Σ ⨟ Γ ⊢c A ! Δ
        → Σ ⨟ Γ ⊢c B ! Δ
        -- Hmm: Should combine opContext from both terms?
        → Σ ⨟ Γ ⊢c B ! Δ
    ⊢A ⨟ ⊢B = `do←— ⊢A 
              `in weakenₑ  ⊢B

    [_]↦_ : {Σ : OpContext} {Γ : Context}
            {Aᵢ Bᵢ B : ValueType}
            {Δ : OpContext}
            {label : String}
            (op : Operation label Aᵢ Bᵢ)
          → {True (Σ ∋-op? op)}
          → Σ ⨟ Γ ∷ Aᵢ ∷ (Bᵢ —→ B ! Δ) ⊢c B ! Δ
          → OpClause Σ Γ Aᵢ Bᵢ B Δ label

    [_]↦_ op {∋?op} ⊢clause = [ op , toWitness ∋?op ]↦ ⊢clause
