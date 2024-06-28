
open import Data.String using (String)
open import Data.Product using (∃-syntax)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩; _,′_ to ⟨_,′_⟩)

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
                 {A : ValueType}
               → (op : Operation)
               → (Σ∋op : Σ ∋-op op)
               → (Δ∋op : Δ ∋-op op)
               → (⊢arg : Σ ⨟ ∅ ⊢v (opArg op))
               → (⊢cont : Σ ⨟ ∅ ▷ (opRet op) ⊢c A ! Δ)
               → Progress (`perform op Σ∋op Δ∋op ⊢arg ⊢cont)

      step  : {A : ValueType} {Δ : OpContext}
            → {⊢c : Σ ⨟ ∅ ⊢c A ! Δ}
            → {⊢c′ : Σ ⨟ ∅ ⊢c A ! Δ}
            → ⊢c ↝ ⊢c′
            → Progress (⊢c)

   ∋op→∋opClause  : {Σ Δ : OpContext} {Γ : Context}
                    {B : ValueType}
                    {op : Operation}
                  → (opClauses : OpClauses Σ Γ B Δ)
                  → (opContext opClauses) ∋-op op
                  → ∃[ ⊢opClause ] ∃[ Σ∋op ] opClauses ∋-opClause ([ op , Σ∋op ]↦ ⊢opClause) 
   ∋op→∋opClause {op = op} (opClauses ▷ opClause@([ .op , Σ∋op ]↦ ⊢clause)) Z = 
      ⟨ ⊢clause , ⟨ Σ∋op , Z opClauses opClause ⟩ ⟩
   ∋op→∋opClause {op = op} (opClauses ▷ ([ _ , _ ]↦ _)) (S ∋op) 
      with ∋op→∋opClause opClauses ∋op
   ... | ⟨ ⊢opClause , ⟨ Σ∋op , ∋opClause ⟩ ⟩ = 
      ⟨ ⊢opClause , ⟨ Σ∋op , S ∋opClause ⟩ ⟩

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
   ... | step exp↝exp′ = step (ξ-do exp↝exp′)
   
   progress (`with `handler _ _ handle `return ⊢v) = 
      step (β-with-return ⊢v)
      
   progress (`with ⊢handler handle ⊢exp@(`do←— _ `in _)) with progress ⊢exp
   ... | step exp↝expr′ = step (ξ-with exp↝expr′)
   
   progress (`with ⊢handler handle ⊢fun-app@(`fun ⊢body `· ⊢arg)) with progress ⊢fun-app 
   ... | step fun-app↝ = step (ξ-with fun-app↝)

   progress (`with ⊢handler handle ⊢if@(`if _ then _ else _)) with progress ⊢if
   ... | step if↝ = step (ξ-with if↝)
   
   progress (`with ⊢handler handle ⊢with@(`with _ handle _)) with progress ⊢with
   ... | step with↝ = step (ξ-with with↝)
   
   progress (`with 
               `handler handler ⊆Δ 
            handle 
               `perform op Σ∋op Δ∋op ⊢arg ⊢exp) with handlerOps handler ∋-op? op
   ... | no ∌op = step (β-with-op-skip ⊢arg ⊢exp  ∌op)
   ... | yes ∋op with ∋op→∋opClause (Handler.ops handler) ∋op
   ... | ⟨ ⊢opClause , ⟨ Σ∋op′ , ∋opClause ⟩ ⟩ 
      = step (β-with-op-handle ∋opClause)
          