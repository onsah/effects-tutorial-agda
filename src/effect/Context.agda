
open import Data.String using (String)
open import Data.String.Properties using (_≟_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import effect.Type
open import effect.Util

module effect.Context where

    infix  4 _∋_
    infix  4 _∋ₑ_
    infixl 5 _∷_

    data Context : Set where
        ∅ : Context
        _∷_ : Context → ValueType → Context

    data _∋_ : Context → ValueType → Set where
        Z : {Γ : Context} {A : ValueType}
          → Γ ∷ A ∋ A
        
        S_ : {Γ : Context} {A B : ValueType}
           → Γ ∋ A
           → Γ ∷ B ∋ A

    -- Unlike Context, this is fixed throughout the whole program.
    -- It's the list of predefined effect signatures that could be used in the program.
    data OpContext : Set where
        ∅ : OpContext
        _∷_ : {label : String} {A B : ValueType}
             → OpContext → Operation label A B → OpContext

    data _∋ₑ_ : {label : String} {A B : ValueType}
              → OpContext → Operation label A B → Set
        where
        Z  : {Γ : OpContext}
              {label : String} {A B : ValueType} 
              {op : Operation label A B}
            → Γ ∷ op ∋ₑ op
        
        S_ : {Γ : OpContext}
              {label label' : String} {A A' B B' : ValueType} 
              {op : Operation label A B} {op' : Operation label' A' B'}
            → Γ ∋ₑ op
            → Γ ∷ op' ∋ₑ op

    _∋ₑ?_ : {A B : ValueType} {label : String}
          → (Σ : OpContext)
          → (op : Operation label A B)
          → Dec (Σ ∋ₑ op)
    ∅ ∋ₑ? op = no (λ())
    _∋ₑ?_ {A = A} {B = B} {label = label} (_∷_ {label = label'} {A = A'} {B = B'} Σ op') op 
      with label ≟ label' | A ≟-v A'  | B ≟-v B'
    ... | no label≢label' | _         | _       = 
      case (Σ ∋ₑ? op) of 
        λ { (yes ∋ₑop) → yes (S ∋ₑop) 
          ; (no ∌ₑop) → no (λ{ Z → label≢label' refl
                              ; (S ∋ₑop) → ∌ₑop ∋ₑop}) }
    ... | yes _           | no A≢A'   | _       = 
      case (Σ ∋ₑ? op) of
        λ { (yes ∋ₑop) → yes (S ∋ₑop)
          ; (no ∌ₑop) → no (λ{ Z → A≢A' refl
                             ; (S ∋ₑop) → ∌ₑop ∋ₑop}) }
    ... | _               | _         | no B≢B' = 
      case (Σ ∋ₑ? op) of
        λ { (yes ∋ₑop) → yes (S ∋ₑop)
          ; (no ∌ₑop) → no (λ{ Z → B≢B' refl
                             ; (S ∋ₑop) → ∌ₑop ∋ₑop})}
    ... | yes refl        | yes refl  | yes refl with op ≟-op op'
    ...   | yes refl                            = yes Z
    ...   | no op≢op' with Σ ∋ₑ? op
    ...     | yes ∋ₑop                          = yes (S ∋ₑop)
    ...     | no ∌ₑop                           = no (λ { Z → op≢op' refl
                                                        ; (S ∋ₑop) → ∌ₑop ∋ₑop})