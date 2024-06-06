
open import Data.String using (String)
open import Data.String.Properties using (_≟_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import effect.Type
open import effect.Util

module effect.Context where

    infix  4 _∋_
    infix  4 _∋ₑ_
    infixl 5 _,_
    infixl 5 _,ₑ_

    data Context : Set where
        ∅ : Context
        _,_ : Context → ValueType → Context

    data _∋_ : Context → ValueType → Set where
        Z : {Γ : Context} {A : ValueType}
          → Γ , A ∋ A
        
        S_ : {Γ : Context} {A B : ValueType}
           → Γ ∋ A
           → Γ , B ∋ A

    -- Unlike Context, this is fixed throughout the whole program.
    -- It's the list of predefined effect signatures that could be used in the program.
    data OpContext : Set where
        ∅ₑ : OpContext
        _,ₑ_ : {label : String} {A B : ValueType}
             → OpContext → Operation label A B → OpContext

    data _∋ₑ_ : {label : String} {A B : ValueType}
              → OpContext → Operation label A B → Set
        where
        Zₑ  : {Γ : OpContext}
              {label : String} {A B : ValueType} 
              {op : Operation label A B}
            → Γ ,ₑ op ∋ₑ op
        
        Sₑ_ : {Γ : OpContext}
              {label label' : String} {A A' B B' : ValueType} 
              {op : Operation label A B} {op' : Operation label' A' B'}
            → Γ ∋ₑ op
            → Γ ,ₑ op' ∋ₑ op

    _∋ₑ?_ : {A B : ValueType} {label : String}
          → (Σ : OpContext)
          → (op : Operation label A B)
          → Dec (Σ ∋ₑ op)
    ∅ₑ ∋ₑ? op = no (λ())
    _∋ₑ?_ {A = A} {B = B} {label = label} (_,ₑ_ {label = label'} {A = A'} {B = B'} Σ op') op 
      with label ≟ label' | A ≟-v A'  | B ≟-v B'
    ... | no label≢label' | _         | _       = 
      case (Σ ∋ₑ? op) of 
        λ { (yes ∋ₑop) → yes (Sₑ ∋ₑop) 
          ; (no ∌ₑop) → no (λ{ Zₑ → label≢label' refl
                              ; (Sₑ ∋ₑop) → ∌ₑop ∋ₑop}) }
    ... | yes _           | no A≢A'   | _       = 
      case (Σ ∋ₑ? op) of
        λ { (yes ∋ₑop) → yes (Sₑ ∋ₑop)
          ; (no ∌ₑop) → no (λ{ Zₑ → A≢A' refl
                             ; (Sₑ ∋ₑop) → ∌ₑop ∋ₑop}) }
    ... | _               | _         | no B≢B' = 
      case (Σ ∋ₑ? op) of
        λ { (yes ∋ₑop) → yes (Sₑ ∋ₑop)
          ; (no ∌ₑop) → no (λ{ Zₑ → B≢B' refl
                             ; (Sₑ ∋ₑop) → ∌ₑop ∋ₑop})}
    ... | yes refl        | yes refl  | yes refl with op ≟-op op'
    ...   | yes refl                            = yes Zₑ
    ...   | no op≢op' with Σ ∋ₑ? op
    ...     | yes ∋ₑop                          = yes (Sₑ ∋ₑop)
    ...     | no ∌ₑop                           = no (λ { Zₑ → op≢op' refl
                                                        ; (Sₑ ∋ₑop) → ∌ₑop ∋ₑop})