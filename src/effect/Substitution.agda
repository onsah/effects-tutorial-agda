
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst)

open import effect.Context
open import effect.Renaming
open import effect.Type
open import effect.Term

module effect.Substitution where

   Substitution   : OpContext → Context → Context → Set
   Substitution   Σ Γ Γ' = 
      {A : ValueType} → Γ ∋ A → Σ ⨟ Γ' ⊢v A

   ext-subst   : {Σ : OpContext}
                 {Γ Γ' : Context} {A : ValueType}
               → Substitution Σ  Γ       Γ'
               → Substitution Σ (Γ ∷ A) (Γ' ∷ A)
   ext-subst σ Z = ` Z
   ext-subst σ (S x) = renameᵥ S_ (σ x)

   subst-c  : {Σ : OpContext} {Δ : OpLabels}
              {Γ Γ' : Context} {A : ValueType}
            → Substitution Σ Γ Γ'
            → Σ ⨟ Γ  ⊢c A ! Δ
            → Σ ⨟ Γ' ⊢c A ! Δ

   subst-v  : {Σ : OpContext}
              {Γ Γ' : Context} {A : ValueType}
            → Substitution Σ Γ Γ'
            → Σ ⨟ Γ  ⊢v A
            → Σ ⨟ Γ' ⊢v A

   subst-ops   : {Σ : OpContext} {Γ Γ' : Context}
               → Substitution Σ Γ Γ'
               → {B : ValueType} {Δ : OpLabels}
               → OpClauses Σ Γ B Δ
               → OpClauses Σ Γ' B Δ
   subst-ops   σ ∅ = ∅
   subst-ops   σ (handlers ∷ [ op , ∋op ]↦ ⊢handler) = 
      (subst-ops σ handlers) ∷ [ op , ∋op ]↦ (subst-c (ext-subst (ext-subst σ)) ⊢handler)

   subst-c σ (`return ⊢A) = `return (subst-v σ ⊢A)
   subst-c σ (`perform op ∋opLabel ∋op ⊢arg ⊢body) = 
      `perform op ∋opLabel ∋op (subst-v σ ⊢arg) (subst-c (ext-subst σ) ⊢body)
   subst-c σ (`do←— ⊢exp `in ⊢body) = 
      `do←— (subst-c σ ⊢exp) `in (subst-c (ext-subst σ) ⊢body)
   subst-c σ (⊢fn `· ⊢arg) = (subst-v σ ⊢fn) `· (subst-v σ ⊢arg)
   subst-c σ (`if ⊢cond then ⊢then else ⊢else) = 
      `if (subst-v σ ⊢cond) then (subst-c σ ⊢then) else (subst-c σ ⊢else)
   subst-c σ (`with ⊢handler handle ⊢exp) = 
      `with (subst-v σ ⊢handler) handle (subst-c σ ⊢exp)

   private
      -- ops under rename doesn't change
      ops-≡-subst : {Σ : OpContext} {Γ Γ' : Context}
                    {B : ValueType} {Δ : OpLabels}
                  → (σ : Substitution Σ Γ Γ')
                  → (handler  : OpClauses Σ Γ B Δ)
                  → (opLabels handler) ≡ (opLabels (subst-ops σ handler))
      ops-≡-subst σ ∅ = refl
      ops-≡-subst σ (handlers ∷ [ label ⦂ _ —→ _ , _ ]↦ ⊢handler) with (ops-≡-subst σ handlers) 
      ... | handlers-≡ = cong (_∷ label) handlers-≡

   subst-v σ (` x) = σ x
   subst-v _ `true = `true
   subst-v _ `false = `false
   subst-v _ `unit = `unit
   subst-v _ (`s x) = `s x
   subst-v σ (`fun ⊢body) = `fun (subst-c (ext-subst σ) ⊢body)
   subst-v σ (`handler  {Δ = Δ} {Δ' = Δ'} handler[ return , ops ] Δ\ops⊆Δ') 
      = `handler handler[ subst-c (ext-subst σ) return , subst-ops σ ops ]
            (subst (λ x → (Δ \' x) ⊆ Δ') (ops-≡-subst σ ops) Δ\ops⊆Δ')
     