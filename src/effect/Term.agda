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

    -- Thought it's appropriate to have effect context as a parameterized type since it's not supposed to change.
    -- Term typing rules are mutually recursive
    -- Can use '⨟' as separater between context
    data _⨟_⊢v_ (Σ : OpContext) (Γ : Context) : ValueType → Set
    -- Hmm: Maybe we should also have OpContext
    data _⨟_⊢c_ (Σ : OpContext) (Γ : Context) : ComputationType → Set

    data HandlerContext (Σ : OpContext) (Γ : Context) 
                        (B : ValueType)
                        (Δ : OpLabels) : Set 
      where
      ∅       : HandlerContext Σ Γ B Δ
      _,[_⇒_] : {label : String} {Aᵢ Bᵢ : ValueType}
              → HandlerContext Σ Γ B Δ
              → (op : Operation label Aᵢ Bᵢ)
              → {True (Σ ∋ₑ? op)}
              → Σ ⨟ Γ , Aᵢ , (Bᵢ —→ B ! Δ) ⊢c B ! Δ
              → HandlerContext Σ Γ B Δ

    -- Asserts that every effect handler body is well typed according to it's effect
    record Handlers  (Σ : OpContext) (Γ : Context) 
                    (A B : ValueType) (Δ : OpLabels) : Set 
      where
      inductive
      field
        return  : Σ ⨟ Γ , A ⊢c B ! Δ
        effects : HandlerContext Σ Γ B Δ

    ops : {Σ : OpContext} {Γ : Context}
          {B : ValueType} {Δ : OpLabels}
        → HandlerContext Σ Γ B Δ 
        → OpLabels
    ops ∅ = ∅ₑₗ
    ops (_,[_⇒_] {label = label} Υ _ _) = (ops Υ) ,ₑₗ label

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
                  → (handlers : Handlers Σ Γ A B Δ')
                  → (Δ \' (ops (Handlers.effects handlers))) ⊆ Δ'
                  → Σ ⨟ Γ ⊢v A ! Δ ⟹ B ! Δ'

    data _⨟_⊢c_ Σ Γ where
        
        `return : {A : ValueType} {Δ : OpLabels}
                → Σ ⨟ Γ ⊢v A
                → Σ ⨟ Γ ⊢c A ! Δ

        -- Op rule
        `op_[_]⇒_ : {Δ : OpLabels} 
                      {A Aₒₚ Bₒₚ : ValueType}
                      {opLabel : String} 
                    → (op : Operation opLabel Aₒₚ Bₒₚ)
                    → {True (Δ ∋ₑₗ? opLabel)}
                    → {True (Σ ∋ₑ? op)}
                    → Σ ⨟ Γ ⊢v Aₒₚ
                    → Σ ⨟ Γ , Bₒₚ ⊢c A ! Δ
                    → Σ ⨟ Γ ⊢c A ! Δ

        `do←—_`in_  : {Δ : OpLabels} 
                      {A B : ValueType}
                    → Σ ⨟ Γ ⊢c A ! Δ
                    → Σ ⨟ Γ , A ⊢c B ! Δ
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

    Rename : Context → Context → Set
    Rename Γ Δ = ∀ {A} → Γ ∋ A → Δ ∋ A

    ext : {Γ Δ : Context}
        → Rename Γ Δ
        → ∀ {B} → Rename (Γ , B) (Δ , B)
    ext ρ Z = Z
    ext ρ (S x) = S (ρ x)

    renameᵥ  : {Σ : OpContext} {Γ Δ : Context}
            → Rename Γ Δ
            → ∀ {A} → Σ ⨟ Γ ⊢v A → Σ ⨟ Δ ⊢v A

    renameₑ  : {Σ : OpContext} {Γ Δ : Context}
            → Rename Γ Δ
            → ∀ {A} → Σ ⨟ Γ ⊢c A → Σ ⨟ Δ ⊢c A

    rename-effects  : {Σ : OpContext} {Γ Γ' : Context}
                → Rename Γ Γ'
                → {B : ValueType} {Δ : OpLabels}
                → HandlerContext Σ Γ B Δ
                → HandlerContext Σ Γ' B Δ
    rename-effects ρ ∅ = ∅
    rename-effects ρ (_,[_⇒_] c op {∋op} handler) = 
      _,[_⇒_] (rename-effects ρ c) op {∋op} (renameₑ (ext (ext ρ)) handler)

    -- ops under rename doesn't change
    ops-≡-rename  : {Σ : OpContext} {Γ Γ' : Context}
                    {B : ValueType} {Δ : OpLabels}
                  → (ρ : Rename Γ Γ')
                  → (handler  : HandlerContext Σ Γ B Δ)
                  → (ops handler) ≡ (ops (rename-effects ρ handler))
    ops-≡-rename ρ ∅ = refl
    ops-≡-rename ρ (handler ,[ op ⇒ x ]) with (ops-≡-rename ρ handler) 
    ... | handler-≡ = cong (_,ₑₗ _) handler-≡

    renameᵥ ρ (` ∋x) = ` (ρ ∋x)
    renameᵥ ρ `true = `true
    renameᵥ ρ `false = `false
    renameᵥ ρ `unit = `unit
    renameᵥ ρ (`s s) = `s s
    renameᵥ ρ (`fun ⊢body) = `fun (renameₑ (ext ρ) ⊢body)
    renameᵥ ρ (`handler {Δ = Δ} {Δ' = Δ'}
                record { 
                  return = return ; 
                  effects = effects 
                } 
                ⊆Δ') = `handler {Δ = Δ}
                    (record { 
                      return = renameₑ (ext ρ) return ; 
                      effects = rename-effects ρ effects
                    }) 
                    (subst (λ x → (Δ \' x) ⊆ Δ') (ops-≡-rename ρ effects) ⊆Δ')
    
    renameₑ ρ (`return ⊢v) = `return (renameᵥ ρ ⊢v)
    renameₑ ρ (`op_[_]⇒_ op {∋ₑₗ?opLabel} {∋ₑ?op} ⊢arg ⊢body) = 
      `op_[_]⇒_ op {∋ₑₗ?opLabel} {∋ₑ?op} 
        (renameᵥ ρ ⊢arg) 
        (renameₑ (ext ρ) ⊢body)
    renameₑ ρ (`do←— ⊢var `in ⊢body) = 
      `do←— (renameₑ ρ ⊢var) `in (renameₑ (ext ρ) ⊢body)
    renameₑ ρ (⊢f `· ⊢g) = (renameᵥ ρ ⊢f) `· (renameᵥ ρ ⊢g)
    renameₑ ρ (`if ⊢cond then ⊢then else ⊢else) = 
      `if (renameᵥ ρ ⊢cond) then (renameₑ ρ ⊢then) else (renameₑ ρ ⊢else)
    renameₑ ρ (`with ⊢handler handle ⊢body) = 
      `with (renameᵥ ρ ⊢handler) handle (renameₑ ρ ⊢body)

    weakenᵥ : {Σ : OpContext}
              {Γ : Context} {A B : ValueType}
            → Σ ⨟ Γ ⊢v A
            → Σ ⨟ Γ , B ⊢v A
    weakenₑ : {Σ : OpContext} {Δ : OpLabels}
              {Γ : Context} {A B : ValueType}
            → Σ ⨟ Γ ⊢c A ! Δ
            → Σ ⨟ Γ , B ⊢c A ! Δ

    weakenᵥ ⊢v = renameᵥ (S_) ⊢v

    weakenₑ ⊢c = renameₑ (S_) ⊢c
  