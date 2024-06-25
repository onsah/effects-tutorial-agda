
open import Data.String using (String)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary.Decidable using (True)
open import Data.String.Properties using (_≟_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong)
open import Relation.Nullary.Negation using (¬_; contraposition)

open import effect.Context
open import effect.Term
open import effect.Type
open import effect.Substitution
open import effect.Renaming

module effect.Reduction where

   infix 3 _↝_

   _[_]  :  {Σ : OpContext} {Γ : Context}
            {C V : ValueType} {Δ : OpContext}
         →  (⊢A : Σ ⨟ Γ ∷ V ⊢c C ! Δ)
         →  (⊢V : Σ ⨟ Γ ⊢v V)
         →  Σ ⨟ Γ ⊢c C ! Δ
   _[_] {Σ = Σ} {Γ = Γ} {V = V} ⊢A ⊢V = subst-c σ ⊢A
      where
      σ : Substitution Σ (Γ ∷ V) Γ
      σ Z = ⊢V
      σ (S ∋A) = ` ∋A

   _[_][_]  :  {Σ : OpContext} {Γ : Context}
               {C V1 V2 : ValueType} {Δ : OpContext}
            →  (⊢C : Σ ⨟ Γ ∷ V1 ∷ V2 ⊢c C ! Δ)
            →  (⊢V1 : Σ ⨟ Γ ⊢v V1)
            →  (⊢V2 : Σ ⨟ Γ ⊢v V2)
            →  Σ ⨟ Γ ⊢c C ! Δ
   _[_][_] {Σ = Σ} {Γ = Γ} {V1 = V1} {V2 = V2} ⊢C ⊢V1 ⊢V2 = 
      subst-c σ ⊢C
      where
      σ : Substitution Σ (Γ ∷ V1 ∷ V2) Γ
      σ Z = ⊢V2
      σ (S Z) = ⊢V1
      σ (S (S ∋A)) = ` ∋A

   data _∋-opClauses_ :  
        {Σ : OpContext} {Γ : Context}
        {Aᵢ Bᵢ B : ValueType}
        {Δ : OpContext} {label : String}
      → OpClauses Σ Γ B Δ
      → OpClause Σ Γ Aᵢ Bᵢ B Δ label
      → Set where
      
      Z  : {Σ : OpContext} {Γ : Context}
           {Aᵢ Bᵢ B : ValueType}
           {Δ : OpContext} {label : String}
         → (opClauses : OpClauses Σ Γ B Δ)
         → (opClause : OpClause Σ Γ Aᵢ Bᵢ B Δ label)
         → (opClauses ∷ opClause) ∋-opClauses opClause

      S_ : {Σ : OpContext} {Γ : Context}
           {Aᵢ Bᵢ B : ValueType}
           {Δ : OpContext} {label : String}
         → (opClauses : OpClauses Σ Γ B Δ)
         → (opClause opClause' : OpClause Σ Γ Aᵢ Bᵢ B Δ label)
         → opClauses ∋-opClauses opClause
         → (opClauses ∷ opClause') ∋-opClauses opClause

   private
      ⊆Δ→∋op'  : {Δ Δ' : OpContext}
                    {label : String} {A B : ValueType}
                    {op : Operation label A B}
                  → Δ ⊆ Δ'
                  → (Δ ∋-op op)
                  → (Δ' ∋-op op)
      ⊆Δ→∋op' {op = op} Δ⊆Δ' ∋label = Δ⊆Δ' op ∋label

      \∋ : {Δ Δ' : OpContext}
           {label : String} {A B : ValueType}
           {op : Operation label A B}
         → (Δ ∋-op op)
         → ¬ (Δ' ∋-op op)
         → Δ \' Δ' ∋-op op
      -- TODO: Understand
      \∋ {Δ = Δ} {Δ' = Δ'} {op = op} Δ∋op ¬Δ'∋op with Δ∋op
      ...     | S_ {op' = op'} Δ₁∋op with Δ' ∋-op? op' 
      ...       | yes Δ'∋op' = \∋ Δ₁∋op ¬Δ'∋op
      ...       | no Δ'∌op' = S \∋ Δ₁∋op ¬Δ'∋op
      \∋ {Δ = Δ} {Δ' = Δ'} {op = op} Δ∋op ¬Δ'∋op | Z with Δ' ∋-op? op 
      ...       | yes Δ'∋op = ⊥-elim (¬Δ'∋op Δ'∋op)
      ...       | no _ = Z

   ⊆Δ→∋op   : {Δ Δ' Δ'' : OpContext}
                 {label : String} {A B : ValueType}
                 {op : Operation label A B}
               → (Δ \' Δ'' ⊆ Δ')
               → (Δ ∋-op op)
               → ¬ (Δ'' ∋-op op)
               → (Δ' ∋-op op)
   ⊆Δ→∋op   {Δ = Δ} {Δ' = Δ'} Δ\⊆Δ' ∋label ¬∋label = 
      -- TODO: `⊆Δ→∋op'` may be redundant
      ⊆Δ→∋op' Δ\⊆Δ' (\∋ ∋label ¬∋label)

   data _↝_ :  {Σ : OpContext} {Γ : Context}
               {A B : ValueType} {Δ Δ' : OpContext}
            →  (⊢A : Σ ⨟ Γ ⊢c A ! Δ)
            →  (⊢B : Σ ⨟ Γ ⊢c B ! Δ')
            →  Set where

      ξ-do        :  {Σ : OpContext} {Γ : Context}
                     {A B : ValueType} {Δ : OpContext}
                     {⊢A ⊢A' : Σ ⨟ Γ ⊢c A ! Δ}
                     {⊢B : Σ ⨟ Γ ∷ A ⊢c B ! Δ}
                  →  ⊢A ↝ ⊢A'
                  →  `do←— ⊢A `in ⊢B ↝ `do←— ⊢A' `in ⊢B

      β-do-return :  {Σ : OpContext} {Γ : Context}
                     {C V : ValueType} {Δ : OpContext}
                  →  (⊢v : Σ ⨟ Γ ⊢v V)
                  →  (⊢c : Σ ⨟ Γ ∷ V ⊢c C ! Δ)
                  → `do←— `return ⊢v `in ⊢c ↝ ⊢c [ ⊢v ]

      β-do-op     :  {Σ : OpContext} {Γ : Context}
                     {A B C D : ValueType} {Δ : OpContext}
                     {opLabel : String} {op : Operation opLabel A B}
                     {Σ∋op : Σ ∋-op op}
                     {Δ∋op : Δ ∋-op op}
                  →  (⊢perform-arg : Σ ⨟ Γ ⊢v A)
                  →  (⊢perform-body : Σ ⨟ Γ ∷ B ⊢c C ! Δ)
                  →  (⊢do-body : Σ ⨟ Γ ∷ C ⊢c D ! Δ)
                  →  (`do←— (`perform op Σ∋op Δ∋op
                              ⊢perform-arg ⊢perform-body) 
                     `in
                        ⊢do-body)
                     ↝ 
                     (`perform op Σ∋op Δ∋op
                        ⊢perform-arg 
                        (`do←— ⊢perform-body `in renameₑ (λ{ Z → Z
                                                         ; (S ∋A) → S (S ∋A)}) ⊢do-body))

      β-if-true   :  {Σ : OpContext} {Γ : Context}
                     {A : ValueType} {Δ : OpContext}
                  →  (⊢then : Σ ⨟ Γ ⊢c A ! Δ)
                  →  (⊢else : Σ ⨟ Γ ⊢c A ! Δ)
                  →  `if `true then ⊢then else ⊢else ↝ ⊢then

      β-if-false  :  {Σ : OpContext} {Γ : Context}
                     {A : ValueType} {Δ : OpContext}
                  →  (⊢then : Σ ⨟ Γ ⊢c A ! Δ)
                  →  (⊢else : Σ ⨟ Γ ⊢c A ! Δ)
                  →  `if `false then ⊢then else ⊢else ↝ ⊢else

      β-fun-app   :  {Σ : OpContext} {Γ : Context}
                     {A B : ValueType} {Δ : OpContext}
                  →  (⊢body : Σ ⨟ Γ ∷ A ⊢c B ! Δ)
                  →  (⊢arg : Σ ⨟ Γ ⊢v A)
                  →  (`fun ⊢body) `· ⊢arg ↝ ⊢body [ ⊢arg ]

      ξ-with      :  {Σ : OpContext} {Γ : Context}
                     {A B : ValueType} {Δ Δ' : OpContext}
                  →  {⊢handler : Σ ⨟ Γ ⊢v A ! Δ' ⟹ B ! Δ}
                  →  {⊢comp₁ ⊢comp₂ : Σ ⨟ Γ ⊢c A ! Δ'}
                  →  (⊢comp₁ ↝ ⊢comp₂)
                  →  (`with ⊢handler handle ⊢comp₁) ↝ (`with ⊢handler handle ⊢comp₂)
                  
      β-with-return  :  {Σ : OpContext} {Γ : Context}
                        {A B : ValueType} {Δ Δ' : OpContext}
                     →  {handlers : Handler Σ Γ A B Δ'}
                     →  {⊆Δ : (Δ \' (opContext (Handler.ops handlers))) ⊆ Δ'}
                     →  (⊢v : Σ ⨟ Γ ⊢v A)
                     →  (`with_handle_ {Δ' = Δ} (`handler handlers ⊆Δ) (`return ⊢v)) 
                        ↝
                        ((Handler.return handlers) [ ⊢v ] )

      β-with-op-handle  :  {Σ : OpContext} {Γ : Context}
                           {A B Aₒₚ Bₒₚ : ValueType} {Δ Δ' : OpContext}
                           {label : String}
                        →  {handler : Handler Σ Γ A B Δ'}
                        →  {⊆Δ : (Δ \' (opContext (Handler.ops handler))) ⊆ Δ'}
                        →  {op : Operation label Aₒₚ Bₒₚ}
                        →  {Σ∋op : Σ ∋-op op}
                        →  {Δ∋op : Δ ∋-op op}
                        →  {⊢v : Σ ⨟ Γ ⊢v Aₒₚ}
                        →  {⊢body : Σ ⨟ Γ ∷ Bₒₚ ⊢c A ! Δ}
                        →  {⊢opClause : Σ ⨟ Γ ∷ Aₒₚ ∷ (Bₒₚ —→ B ! Δ') ⊢c B ! Δ'}
                        →  ((Handler.ops handler) ∋-opClauses ([ op , Σ∋op ]↦ ⊢opClause))
                        →  `with (`handler handler ⊆Δ) 
                           handle (`perform op Σ∋op Δ∋op ⊢v ⊢body)
                           ↝
                           ⊢opClause [ ⊢v ][ 
                              `fun (
                                 `with weakenᵥ (`handler handler ⊆Δ) 
                                 handle ⊢body) 
                           ]

      β-with-op-skip :  {Σ : OpContext} {Γ : Context}
                        {A B Aₒₚ Bₒₚ : ValueType} {Δ Δ' : OpContext}
                        {label : String}
                     →  {handler : Handler Σ Γ A B Δ'}
                     →  {⊆Δ : (Δ \' (opContext (Handler.ops handler))) ⊆ Δ'}
                     →  {op : Operation label Aₒₚ Bₒₚ}
                     →  {Σ∋op : Σ ∋-op op}
                     →  {Δ∋op : Δ ∋-op op}
                     →  {⊢v : Σ ⨟ Γ ⊢v Aₒₚ}
                     →  {⊢body : Σ ⨟ Γ ∷ Bₒₚ ⊢c A ! Δ}
                     →  {⊢opClause : Σ ⨟ Γ ∷ Aₒₚ ∷ (Bₒₚ —→ B ! Δ') ⊢c B ! Δ'}
                     →  (¬∋op : ¬ (opContext (Handler.ops handler) ∋-op op))
                     →  `with (`handler handler ⊆Δ) 
                        handle (`perform op Σ∋op Δ∋op ⊢v ⊢body)
                        ↝
                        `perform op Σ∋op (⊆Δ→∋op ⊆Δ Δ∋op ¬∋op) 
                           ⊢v
                           (`with weakenᵥ (`handler handler ⊆Δ)
                           handle ⊢body)
         