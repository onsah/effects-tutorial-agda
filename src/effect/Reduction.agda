
open import Data.String using (String)
open import Relation.Nullary.Decidable using (True)

open import effect.Context
open import effect.Term
open import effect.Type
open import effect.Substitution
open import effect.Renaming

module effect.Reduction where

   infix 3 _↝_

   _[_]  :  {Σ : OpContext} {Γ : Context}
            {C V : ValueType} {Δ : OpLabels}
         →  (⊢A : Σ ⨟ Γ , V ⊢c C ! Δ)
         →  (⊢V : Σ ⨟ Γ ⊢v V)
         →  Σ ⨟ Γ ⊢c C ! Δ
   _[_] {Σ = Σ} {Γ = Γ} {V = V} ⊢A ⊢V = subst-c σ ⊢A
      where
      σ : Substitution Σ (Γ , V) Γ
      σ Z = ⊢V
      σ (S ∋A) = ` ∋A

   _[_][_]  :  {Σ : OpContext} {Γ : Context}
               {C V1 V2 : ValueType} {Δ : OpLabels}
            →  (⊢C : Σ ⨟ Γ , V1 , V2 ⊢c C ! Δ)
            →  (⊢V1 : Σ ⨟ Γ ⊢v V1)
            →  (⊢V2 : Σ ⨟ Γ ⊢v V2)
            →  Σ ⨟ Γ ⊢c C ! Δ
   _[_][_] {Σ = Σ} {Γ = Γ} {V1 = V1} {V2 = V2} ⊢C ⊢V1 ⊢V2 = 
      subst-c σ ⊢C
      where
      σ : Substitution Σ (Γ , V1 , V2) Γ
      σ Z = ⊢V2
      σ (S Z) = ⊢V1
      σ (S (S ∋A)) = ` ∋A
   

   data _↝_ :  {Σ : OpContext} {Γ : Context}
               {A B : ValueType} {Δ Δ' : OpLabels}
            →  (⊢A : Σ ⨟ Γ ⊢c A ! Δ)
            →  (⊢B : Σ ⨟ Γ ⊢c B ! Δ')
            →  Set where

      ξ-do        :  {Σ : OpContext} {Γ : Context}
                     {A B : ValueType} {Δ : OpLabels}
                     {⊢A ⊢A' : Σ ⨟ Γ ⊢c A ! Δ}
                     {⊢B : Σ ⨟ Γ , A ⊢c B ! Δ}
                  →  ⊢A ↝ ⊢A'
                  →  `do←— ⊢A `in ⊢B ↝ `do←— ⊢A' `in ⊢B

      β-do-return :  {Σ : OpContext} {Γ : Context}
                     {C V : ValueType} {Δ : OpLabels}
                  →  {⊢V : Σ ⨟ Γ ⊢v V}
                  →  {⊢C : Σ ⨟ Γ , V ⊢c C ! Δ}
                  → `do←— `return ⊢V `in ⊢C ↝ ⊢C [ ⊢V ]

      β-do-op     :  {Σ : OpContext} {Γ : Context}
                     {A B C D : ValueType} {Δ : OpLabels}
                     {opLabel : String} {op : Operation opLabel A B}
                     {∋?opLabel : True (Δ ∋-oL? opLabel)}
                     {∋?op : True (Σ ∋ₑ? op)}
                  →  (⊢perform-arg : Σ ⨟ Γ ⊢v A)
                  →  (⊢perform-body : Σ ⨟ Γ , B ⊢c C ! Δ)
                  →  (⊢do-body : Σ ⨟ Γ , C ⊢c D ! Δ)
                  →  (`do←— (`perform op ∋?opLabel ∋?op 
                              ⊢perform-arg ⊢perform-body) 
                     `in
                        ⊢do-body)
                     ↝ 
                     (`perform op ∋?opLabel ∋?op 
                        ⊢perform-arg 
                        (`do←— ⊢perform-body `in renameₑ (λ{ Z → Z
                                                         ; (S ∋A) → S (S ∋A)}) ⊢do-body))

      β-if-true   :  {Σ : OpContext} {Γ : Context}
                     {A B : ValueType} {Δ : OpLabels}
                  →  {⊢then : Σ ⨟ Γ ⊢c A ! Δ}
                  →  {⊢else : Σ ⨟ Γ ⊢c A ! Δ}
                  →  `if `true then ⊢then else ⊢else ↝ ⊢then

      β-if-false  :  {Σ : OpContext} {Γ : Context}
                     {A B : ValueType} {Δ : OpLabels}
                  →  {⊢then : Σ ⨟ Γ ⊢c A ! Δ}
                  →  {⊢else : Σ ⨟ Γ ⊢c A ! Δ}
                  →  `if `false then ⊢then else ⊢else ↝ ⊢else

      β-fun-app   :  {Σ : OpContext} {Γ : Context}
                     {A B : ValueType} {Δ : OpLabels}
                  →  {⊢body : Σ ⨟ Γ , A ⊢c B ! Δ}
                  →  {⊢arg : Σ ⨟ Γ ⊢v A}
                  →  (`fun ⊢body) `· ⊢arg ↝ ⊢body [ ⊢arg ]

      ξ-with      :  {Σ : OpContext} {Γ : Context}
                     {A B : ValueType} {Δ Δ' : OpLabels}
                  →  {⊢handler : Σ ⨟ Γ ⊢v A ! Δ' ⟹ B ! Δ}
                  →  {⊢comp₁ ⊢comp₂ : Σ ⨟ Γ ⊢c A ! Δ'}
                  →  (⊢comp₁ ↝ ⊢comp₂)
                  →  (`with ⊢handler handle ⊢comp₁) ↝ (`with ⊢handler handle ⊢comp₂)
                  
      β-with-return  :  {Σ : OpContext} {Γ : Context}
                        {A B : ValueType} {Δ Δ' : OpLabels}
                     →  {handlers : Handler Σ Γ A B Δ'}
                     →  {⊆Δ : (Δ \' (opLabels (Handler.ops handlers))) ⊆ Δ'}
                     →  {⊢v : Σ ⨟ Γ ⊢v A}
                     →  (`with_handle_ {Δ' = Δ} (`handler handlers ⊆Δ) (`return ⊢v)) 
                        ↝
                        ((Handler.return handlers) [ ⊢v ] )

      {- β-with-op-handle  :  {Σ : OpContext} {Γ : Context}
                           {A B : ValueType} {Δ Δ' : OpLabels}
                        →  {handlers : Handler Σ Γ A B Δ'}
                        →  {⊆Δ : (Δ \' (opLabels (Handler.ops handlers))) ⊆ Δ'}
                        →  {⊢v : Σ ⨟ Γ ⊢v A}      
                        →  {op : ...}
                        →  {handler : ...}
                        →  ((Handler.ops handlers) ∋[ op , handler ])
                        →  ...


      β-with-op-handle  :  {Σ : OpContext} {Γ : Context}
                           {A B : ValueType} {Δ Δ' : OpLabels}
                        →  {handlers : Handler Σ Γ A B Δ'}
                        →  {⊆Δ : (Δ \' (opLabels (Handler.ops handlers))) ⊆ Δ'}
                        →  {⊢v : Σ ⨟ Γ ⊢v A}      
                        →  {op : ...}
                        →  {handler : ...}
                        →  ¬ ((Handler.ops handlers) ∋[ op , handler ])    -}                     
 
    