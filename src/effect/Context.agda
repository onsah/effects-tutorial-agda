
open import Data.String using (String)
open import Data.String.Properties using (_≟_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import effect.Type
open import effect.Util

module effect.Context where

   infix  4 _∋_
   infixl 5 _▷_
   infix  7 S_

   data Context : Set where
      ∅ : Context
      _▷_ : Context → ValueType → Context

   data _∋_ : Context → ValueType → Set where
      Z  : {Γ : Context} {A : ValueType}
         → Γ ▷ A ∋ A
        
      S_ : {Γ : Context} {A B : ValueType}
         → Γ ∋ A
         → Γ ▷ B ∋ A
