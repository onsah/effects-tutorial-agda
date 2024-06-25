
open import Data.String using (String)

open import effect.Type
open import effect.Context
open import effect.Term
open import effect.Reduction

-- a.k.a. Safety
module effect.Progress (Σ : OpContext) where
   
   data Progress  : {A : ValueType} {Δ : OpContext}
                  → Σ ⨟ ∅ ⊢c A ! Δ → Set
      where

      done-value  : {A : ValueType} {Δ : OpContext}
            → (⊢v : Σ ⨟ ∅ ⊢v A)
            → Progress {Δ = Δ} (`return ⊢v)

      done-op  : {Δ : OpContext} 
                 {A Aₒₚ Bₒₚ : ValueType}
                 {opLabel : String} 
               → (op : Operation opLabel Aₒₚ Bₒₚ)
               → (Σ∋op : Σ ∋-op op)
               → (Δ∋op : Δ ∋-op op)
               → (⊢arg : Σ ⨟ ∅ ⊢v Aₒₚ)
               → (⊢cont : Σ ⨟ ∅ ∷ Bₒₚ ⊢c A ! Δ)
               → Progress (`perform op Σ∋op Δ∋op ⊢arg ⊢cont)

      step  : {A : ValueType} {Δ : OpContext}
            → {⊢c : Σ ⨟ ∅ ⊢c A ! Δ}
            → {⊢c′ : Σ ⨟ ∅ ⊢c A ! Δ}
            → ⊢c ↝ ⊢c′
            → Progress (⊢c)

   progress : {A : ValueType} {Δ : OpContext}
            → (⊢c : Σ ⨟ ∅ ⊢c A ! Δ)
            → Progress ⊢c
   progress (`return ⊢v) = done-value ⊢v

   progress (`perform op Σ∋op Δ∋op ⊢arg ⊢body) = 
      done-op op Σ∋op Δ∋op ⊢arg ⊢body
   progress (`fun ⊢body `· ⊢arg) = step (β-fun-app ⊢body ⊢arg)
   
   progress (`if `true then ⊢then else ⊢else) = step (β-if-true ⊢then ⊢else)
   
   progress (`if `false then ⊢then else ⊢else) = step (β-if-false ⊢then ⊢else)
   
   progress (`do←— `return ⊢v `in ⊢body) = step (β-do-return ⊢v ⊢body)
   
   progress (`do←— `perform _ _ _ ⊢arg ⊢cont `in ⊢body) = 
      step (β-do-op ⊢arg ⊢cont ⊢body)

   progress (`do←— ⊢exp `in ⊢body) with progress ⊢exp
   ... | done-value ⊢v = step (β-do-return ⊢v ⊢body)
   ... | done-op _ _ _ ⊢arg ⊢cont = step (β-do-op ⊢arg ⊢cont ⊢body)
   ... | step exp↝exp→′ = step (ξ-do exp↝exp→′)
   
   progress (`with `handler _ _ handle `return ⊢v) = 
      step (β-with-return ⊢v)
   progress (`with ⊢handler handle (`do←— ⊢exp `in ⊢exp₁)) = {!   !}
   progress (`with ⊢handler handle (x `· x₁)) = {!   !}
   progress (`with ⊢handler handle `if x then ⊢exp else ⊢exp₁) = {!   !}
   progress (`with ⊢handler handle (`with x handle ⊢exp)) = {!   !}
   progress (`with ⊢handler handle `perform op Σ∋op Δ∋op ⊢arg ⊢exp) = {!   !}
       