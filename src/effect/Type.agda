open import Data.String using (String)
open import Data.String.Properties using (_≟_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩; _,′_ to ⟨_,′_⟩)

module effect.Type where
    
   infix  4 _∋-op_
   infixl 5 _▷_
   infix 6 _!_
   infixr 5 _—→_
   infix 5 _⟹_
   infix 5 _⦂_—→_
   infix 10 _\'_
   infix 9 _⊆_
   infix 6 S_⨾_

   data ValueType : Set
   data ComputationType : Set
   data Operation : Set
   data OpContext : Set

   data ValueType where
      bool : ValueType
      str  : ValueType
      int  : ValueType
      unit : ValueType
      void : ValueType
      _—→_ : ValueType → ComputationType → ValueType
      _⟹_ : ComputationType → ComputationType → ValueType

   data ComputationType where
      -- OpContext is an overappromixation of what the computation actually uses.
      _!_ : ValueType → OpContext → ComputationType

   data Operation where
      _⦂_—→_   : (label : String) → (A : ValueType) → (B : ValueType) 
               → Operation
   
   opLabel  : Operation → String
   opLabel (label ⦂ _ —→ _) = label

   opArg : Operation → ValueType
   opArg (_ ⦂ A —→ _) = A

   opRet : Operation → ValueType
   opRet (_ ⦂ _ —→ B) = B
    
   data OpContext where
      ∅     : OpContext
      
      _▷_   : OpContext → Operation → OpContext

   _≟-v_ : (A : ValueType)
         → (B : ValueType)
         → Dec (A ≡ B)
   _≟-c_ : (A : ComputationType)
         → (B : ComputationType)
         → Dec (A ≡ B)
   _≟-Δ_ : (Δ : OpContext)
         → (Δ' : OpContext)
         → Dec (Δ ≡ Δ')
    
   bool ≟-v bool = yes refl
   str ≟-v str = yes refl
   int ≟-v int = yes refl
   unit ≟-v unit = yes refl
   (A —→ B) ≟-v (A' —→ B') with A ≟-v A' | B ≟-c B'
   ... | yes refl  | yes refl  = yes refl
   ... | no A≢A'   | _         = no λ{ refl → A≢A' refl}
   ... | _         | no B≢B'   = no λ{ refl → B≢B' refl}
   (A ⟹ B) ≟-v (A' ⟹ B') with A ≟-c A' | B ≟-c B'
   ... | yes refl  | yes refl  = yes refl
   ... | no A≢A'   | _         = no λ{ refl → A≢A' refl}
   ... | _         | no B≢B'   = no λ{ refl → B≢B' refl}
   bool ≟-v str = no (λ())
   bool ≟-v int = no (λ())
   bool ≟-v unit = no (λ())
   bool ≟-v void = no (λ())
   bool ≟-v (_ —→ _) = no (λ())
   bool ≟-v (_ ⟹ _) = no (λ())
   str ≟-v bool = no (λ())
   str ≟-v int = no (λ())
   str ≟-v unit = no (λ())
   str ≟-v void = no (λ())
   str ≟-v (_ —→ _) = no (λ())
   str ≟-v (_ ⟹ _) = no (λ())
   int ≟-v bool = no (λ())
   int ≟-v str = no (λ())
   int ≟-v unit = no (λ())
   int ≟-v void = no (λ())
   int ≟-v (_ —→ _) = no (λ())
   int ≟-v (_ ⟹ _) = no (λ())
   unit ≟-v bool = no (λ())
   unit ≟-v str = no (λ())
   unit ≟-v int = no (λ())
   unit ≟-v void = no (λ())
   unit ≟-v (_ —→ _) = no (λ())
   unit ≟-v (_ ⟹ _) = no (λ())
   void ≟-v bool = no (λ())
   void ≟-v str = no (λ())
   void ≟-v int = no (λ())
   void ≟-v unit = no (λ())
   void ≟-v void = yes refl
   void ≟-v (_ —→ _) = no (λ())
   void ≟-v (_ ⟹ _) = no (λ())
   (_ —→ _) ≟-v bool = no (λ())
   (_ —→ _) ≟-v str = no (λ())
   (_ —→ _) ≟-v int = no (λ())
   (_ —→ _) ≟-v unit = no (λ())
   (_ —→ _) ≟-v void = no (λ())
   (_ —→ _) ≟-v (_ ⟹ _) = no (λ())
   (_ ⟹ _) ≟-v bool = no (λ())
   (_ ⟹ _) ≟-v str = no (λ())
   (_ ⟹ _) ≟-v int = no (λ())
   (_ ⟹ _) ≟-v unit = no (λ())
   (_ ⟹ _) ≟-v void = no (λ())
   (_ ⟹ _) ≟-v (_ —→ _) = no (λ())

   (x₁ ! Δ₁) ≟-c (x₂ ! Δ₂) with x₁ ≟-v x₂ | Δ₁ ≟-Δ Δ₂
   ... | _         | no Δ₁≢Δ₂  = no λ { refl → Δ₁≢Δ₂ refl}
   ... | no x₁≢x₂  | _         = no λ { refl → x₁≢x₂ refl}
   ... | yes refl  | yes refl  = yes refl

   ∅ ≟-Δ ∅ = yes refl
   ∅ ≟-Δ (Δ₂ ▷ x) = no (λ())
   (_ ▷ _) ≟-Δ ∅ = no (λ())
   (Δ ▷ (label ⦂ A —→ B)) ≟-Δ (Δ' ▷ (label' ⦂ A' —→ B')) with Δ ≟-Δ Δ'
   ... | no ¬Δ≡Δ = no (λ{ refl → ¬Δ≡Δ refl})
   ... | yes Δ≡Δ' with label ≟ label' | A ≟-v A' | B ≟-v B'
   ...   | no label≢label    | _         | _         = no (λ{ refl → label≢label refl})
   ...   | _                 | no A≢A    | _         = no (λ{ refl → A≢A refl})
   ...   | _                 | _         | no B≢B    = no (λ{ refl → B≢B refl})
   ...   | yes refl          | yes refl  | yes refl = yes (cong (_▷ (label ⦂ A —→ B)) Δ≡Δ')

   data _∋-op_   : OpContext → Operation → Set 
      where
      Z  : {Δ : OpContext}
           {op : Operation}
         → Δ ▷ op ∋-op op
      
      S_⨾_  : {Δ : OpContext}
           {op op′ : Operation}
         → Δ ∋-op op
         → ¬ (op ≡ op′)
         → Δ ▷ op′ ∋-op op

   _≟-op_   : (op op′ : Operation)
            → Dec (op ≡ op′)
   (label ⦂ A —→ B) ≟-op (label' ⦂ A' —→ B') with label ≟ label' | A ≟-v A' | B ≟-v B' 
   ... | yes refl        | yes refl  | yes refl  = yes refl
   ... | no label≢label' | _         | _         = no λ  {refl → label≢label' refl}
   ... | _               | no A≢A'   | _         = no λ  {refl → A≢A' refl}
   ... | _               | _         | no B≢B'   = no λ  {refl → B≢B' refl}

   _∋-op?_  : (Δ : OpContext) 
            → (op : Operation)
            → Dec (Δ ∋-op op)

   ∅ ∋-op? _ = no (λ())
   (Δ ▷ op′) ∋-op? op with op ≟-op op′
   ... | yes refl = yes Z
   ... | no op≢op′ with Δ ∋-op? op
   ...   | yes Δ∋op = yes (S Δ∋op ⨾ op≢op′)
   ...   | no Δ∌op = no (λ{ Z → op≢op′ refl
                          ; (S Δ∋op ⨾ _) → Δ∌op Δ∋op})

   _⊆_ : OpContext → OpContext → Set
   Δ ⊆ Δ' =   (op : Operation) 
            → Δ ∋-op op → Δ' ∋-op op

   _\'_ : OpContext → OpContext → OpContext
   ∅ \' Δ' = ∅
   (Δ ▷ op) \' Δ' with Δ' ∋-op? op
   ... | yes _ = Δ \' Δ'
   ... | no  _ = (Δ \' Δ') ▷ op
  