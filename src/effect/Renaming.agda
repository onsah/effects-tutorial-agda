
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst)

open import effect.Context
open import effect.Term
open import effect.Type

module effect.Renaming where
   Renaming : Context → Context → Set
   Renaming Γ Δ = ∀ {A} → Γ ∋ A → Δ ∋ A

   private
      ext : {Γ Δ : Context}
          → Renaming Γ Δ
          → ∀ {B} → Renaming (Γ , B) (Δ , B)
      ext ρ Z = Z
      ext ρ (S x) = S (ρ x)

   renameᵥ  : {Σ : OpContext} {Γ Δ : Context}
            → Renaming Γ Δ
            → ∀ {A} → Σ ⨟ Γ ⊢v A → Σ ⨟ Δ ⊢v A

   renameₑ  : {Σ : OpContext} {Γ Δ : Context}
            → Renaming Γ Δ
            → ∀ {A} → Σ ⨟ Γ ⊢c A → Σ ⨟ Δ ⊢c A

   rename-ops  : {Σ : OpContext} {Γ Γ' : Context}
               → Renaming Γ Γ'
               → {B : ValueType} {Δ : OpLabels}
               → OpHandlers Σ Γ B Δ
               → OpHandlers Σ Γ' B Δ
   rename-ops ρ ∅ = ∅
   rename-ops ρ (c ∷[ op , ∋op ⇒ handler ]) = 
      (rename-ops ρ c) ∷[ op , ∋op ⇒ (renameₑ (ext (ext ρ)) handler) ]

   private
      -- ops under rename doesn't change
      ops-≡-rename  : {Σ : OpContext} {Γ Γ' : Context}
                      {B : ValueType} {Δ : OpLabels}
                    → (ρ : Renaming Γ Γ')
                    → (handler  : OpHandlers Σ Γ B Δ)
                    → (opLabels handler) ≡ (opLabels (rename-ops ρ handler))
      ops-≡-rename ρ ∅ = refl
      ops-≡-rename ρ (handler ∷[ op , _ ⇒ _ ]) with (ops-≡-rename ρ handler) 
      ... | handler-≡ = cong (_, _) handler-≡

   renameᵥ ρ (` ∋x) = ` (ρ ∋x)
   renameᵥ ρ `true = `true
   renameᵥ ρ `false = `false
   renameᵥ ρ `unit = `unit
   renameᵥ ρ (`s s) = `s s
   renameᵥ ρ (`fun ⊢body) = `fun (renameₑ (ext ρ) ⊢body)
   renameᵥ ρ (`handler {Δ = Δ} {Δ' = Δ'}
               record { 
                  return = return ; 
                  ops = ops 
               } 
               ⊆Δ') = `handler {Δ = Δ}
                  (record { 
                     return = renameₑ (ext ρ) return ; 
                     ops = rename-ops ρ ops
                  }) 
                  (subst (λ x → (Δ \' x) ⊆ Δ') (ops-≡-rename ρ ops) ⊆Δ')
    
   renameₑ ρ (`return ⊢v) = `return (renameᵥ ρ ⊢v)
   renameₑ ρ (`perform op ∋-oL?opLabel ∋ₑ?op ⊢arg ⊢body) = 
      `perform op ∋-oL?opLabel ∋ₑ?op 
        (renameᵥ ρ ⊢arg) 
        (renameₑ (ext ρ) ⊢body)
   renameₑ ρ (`do←— ⊢var `in ⊢body) = 
      `do←— (renameₑ ρ ⊢var) `in (renameₑ (ext ρ) ⊢body)
   renameₑ ρ (⊢f `· ⊢g) = (renameᵥ ρ ⊢f) `· (renameᵥ ρ ⊢g)
   renameₑ ρ (`if ⊢cond then ⊢then else ⊢else) = 
      `if (renameᵥ ρ ⊢cond) then (renameₑ ρ ⊢then) else (renameₑ ρ ⊢else)
   renameₑ ρ (`with ⊢handler handle ⊢body) = 
      `with (renameᵥ ρ ⊢handler) handle (renameₑ ρ ⊢body)

   weakenᵥ  :  {Σ : OpContext}
               {Γ : Context} {A B : ValueType}
            →  Σ ⨟ Γ ⊢v A
            →  Σ ⨟ Γ , B ⊢v A
   weakenₑ  :  {Σ : OpContext} {Δ : OpLabels}
               {Γ : Context} {A B : ValueType}
            →  Σ ⨟ Γ ⊢c A ! Δ
            →  Σ ⨟ Γ , B ⊢c A ! Δ

   weakenᵥ ⊢v = renameᵥ (S_) ⊢v

   weakenₑ ⊢c = renameₑ (S_) ⊢c
  
