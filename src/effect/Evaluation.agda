
open import Data.Nat using (ℕ; suc; zero)
open import Data.Fin using (Fin; suc)
open import Relation.Nullary.Negation using (¬_)
open import Data.Product using (∃-syntax)

open import effect.Reduction
open import effect.Term
open import effect.Type
open import effect.Context
open import effect.Progress

module effect.Evaluation where

   infix  2 _—↠_
   infixr 2 _—→⟨_⟩_
   infix  3 _∎

   record Gas : Set where
      constructor gas
      field
         amount : ℕ

   data Done  {Σ Δ : OpContext} {Γ : Context}
              {A : ValueType}
            : (term : Σ ⨟ Γ ⊢c A ! Δ) 
            → Set where
      
      done-return : (⊢v : Σ ⨟ Γ ⊢v A)
                  → Done (`return {Δ = Δ} ⊢v)

      done-perform   : {op : Operation} {Σ∋op : Σ ∋-op op}
                       {Δ∋op : Δ ∋-op op}
                     → (⊢arg : Σ ⨟ Γ ⊢v (opArg op))
                     → (⊢cont : Σ ⨟ Γ ▷ (opRet op) ⊢c A ! Δ)
                     → Done (`perform op Σ∋op Δ∋op ⊢arg ⊢cont) 

   data Finished {Σ Δ : OpContext} {Γ : Context}
                 {A : ValueType}
                 (⊢c : Σ ⨟ Γ ⊢c A ! Δ)
               : Set where
      
      done  : Done ⊢c
            → Finished ⊢c

      out-of-gas  : Finished ⊢c
   
   data _—↠_ {Σ Δ : OpContext} {Γ : Context}
             {A : ValueType}
            : Σ ⨟ Γ ⊢c A ! Δ
            → Σ ⨟ Γ ⊢c A ! Δ
            → Set where
      
      _∎ : (⊢c : Σ ⨟ Γ ⊢c A ! Δ)
         → ⊢c —↠ ⊢c

      step—→   : (⊢c : Σ ⨟ Γ ⊢c A ! Δ) {⊢c′ ⊢c′′ : Σ ⨟ Γ ⊢c A ! Δ}
               → ⊢c′ —↠ ⊢c′′
               → ⊢c ↝ ⊢c′
               → ⊢c —↠ ⊢c′′

   pattern _—→⟨_⟩_ L L—→M M—↠N = step—→ L M—↠N L—→M                             

   data Steps {Δ : OpContext} {A : ValueType}
              {Σ : OpContext}
            : (Σ ⨟ ∅ ⊢c A ! Δ)
            → Set 
      where

      steps : {⊢c ⊢c′ : Σ ⨟ ∅ ⊢c A ! Δ}
            → ⊢c —↠ ⊢c′
            → Finished ⊢c′
            → Steps ⊢c
            

   eval  : {Δ : OpContext} {A : ValueType}
           {Σ : OpContext}
         → Gas
         → (⊢c : Σ ⨟ ∅ ⊢c A ! Δ)
         → Steps ⊢c
   eval (gas zero) ⊢c = steps (⊢c ∎) out-of-gas
   eval (gas (suc amount)) ⊢c with progress _ ⊢c
   ... | done-value ⊢v = 
            steps (⊢c ∎) (done (done-return ⊢v))
   ... | done-op _ _ _ ⊢arg ⊢cont =
            steps (⊢c ∎) (done (done-perform ⊢arg ⊢cont))
   ... | step {⊢c′ = ⊢c′} ⊢c↝⊢c′ with eval (gas amount) ⊢c′
   ...   | steps ⊢c′—↠⊢c′′ fin = 
            steps (⊢c —→⟨ ⊢c↝⊢c′ ⟩ ⊢c′—↠⊢c′′) fin
   
