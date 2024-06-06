
open import Data.String using (String)
open import Relation.Nullary.Decidable using (True)
open import Data.Nat using (ℕ)

open import effect.Type
open import effect.Context
open import effect.Term

module effect.SyntaxSugar where

    opCall[_] : {A B : ValueType}
                {Σ : OpContext} {Δ : OpLabels}
                {opLabel : String}
              → (op : Operation opLabel A B)
              → {True (Δ ∋-oL? opLabel)}
              → {True (Σ ∋ₑ? op)}
              → Σ ⨟ ∅ ⊢v A —→ B ! Δ
    opCall[_] op {∋?opLabel} {∋ₑ?op} =
      `fun (`op_[_]⇒_ op {∋?opLabel} {∋ₑ?op} (` Z) (`return (` Z)))

    open import Data.Nat using (_<_; _≤?_; zero; suc; s≤s)
    open import Relation.Nullary.Decidable using (toWitness)

    private
      length  : Context → ℕ
      length ∅ = zero
      length (Γ , _) = suc (length Γ)

      lookup  : {Γ : Context} → {n : ℕ}
              → (p : n < length Γ)
              → ValueType
      lookup {Γ = _ , A} {n = zero} _ = A
      lookup {Γ = _ , _} {n = suc _} (s≤s p) = (lookup p)

      count   : {Γ : Context} → {n : ℕ}
              → (p : n < length Γ)
              → Γ ∋ lookup p
      count {Γ = _ , _} {n = zero } _ = Z
      count {Γ = _ , _} {n = suc _} (s≤s p) = S (count p)

    
    #_ : ∀ {Γ : Context} {Σ : OpContext}
      → (n : ℕ)
      → {n∈Γ : True (suc n ≤? length Γ)}
        --------------------------------
      → Σ ⨟ Γ ⊢v lookup (toWitness n∈Γ)
    #_ _ {n∈Γ = n∈Γ}  = ` (count (toWitness n∈Γ))