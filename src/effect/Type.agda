open import Data.String using (String)
open import Data.String.Properties using (_≟_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩; _,′_ to ⟨_,′_⟩)

module effect.Type where
    
   infix  4 _∋-op_
   infixl 5 _∷_
   infix 6 _!_
   infixr 5 _—→_
   infix 5 _⟹_
   infix 5 _⦂_—→_
   infix 10 _\'_
   infix 9 _⊆_

   data ValueType : Set
   data ComputationType : Set
   data Operation : String → ValueType → ValueType → Set
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
               → Operation label A B
    
   data OpContext where
      ∅     : OpContext
      _∷_   : {label : String} {A B : ValueType}
            → OpContext → Operation label A B → OpContext

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
   ∅ ≟-Δ (Δ₂ ∷ x) = no (λ())
   (_ ∷ _) ≟-Δ ∅ = no (λ())
   (Δ ∷ (label ⦂ A —→ B)) ≟-Δ (Δ' ∷ (label' ⦂ A' —→ B')) with Δ ≟-Δ Δ'
   ... | no ¬Δ≡Δ = no (λ{ refl → ¬Δ≡Δ refl})
   ... | yes Δ≡Δ' with label ≟ label' | A ≟-v A' | B ≟-v B'
   ...   | no label≢label    | _         | _         = no (λ{ refl → label≢label refl})
   ...   | _                 | no A≢A    | _         = no (λ{ refl → A≢A refl})
   ...   | _                 | _         | no B≢B    = no (λ{ refl → B≢B refl})
   ...   | yes refl          | yes refl  | yes refl = yes (cong (_∷ (label ⦂ A —→ B)) Δ≡Δ')

   data _∋-op_   : {label : String} {A B : ValueType}
               → OpContext → Operation label A B → Set 
      where
      Z  : {Δ : OpContext}
            {label : String} {A B : ValueType}
            {op : Operation label A B}
         → Δ ∷ op ∋-op op
      
      S_ : {Δ : OpContext}
            {label label' : String} {A A' B B' : ValueType}
            {op : Operation label A B} {op' : Operation label' A' B'}
         -- → ¬ (op ≡ op')
         → Δ ∋-op op
         → Δ ∷ op' ∋-op op

   _∋-op?_  : {label : String} {A B : ValueType}
              (Δ : OpContext) 
            → (op : Operation label A B)
            → Dec (Δ ∋-op op)

   ∅ ∋-op? _ = no (λ())
   (Δ ∷ (label ⦂ A —→ B)) ∋-op? op@(label' ⦂ A' —→ B') with label ≟ label' | A ≟-v A' | B ≟-v B' | Δ ∋-op? op
   ...   | yes refl          | yes refl  | yes refl | _       = yes Z
   ...   | no label≢label    | _         | _        | yes ∋op = yes (S ∋op)
   ...   | no label≢label    | _         | _        | no ∌op  = no (λ{ Z → label≢label refl
                                                                     ; (S ∋op) → ∌op ∋op})
   ...   | _                 | no A≢A    | _        | yes ∋op = yes (S ∋op)
   ...   | _                 | no A≢A    | _        | no ∌op  = no (λ{ Z → A≢A refl
                                                                     ; (S ∋op) → ∌op ∋op})
   ...   | _                 | _         | no B≢B   | yes ∋op = yes (S ∋op)
   ...   | _                 | _         | no B≢B   | no ∌op  = no (λ{ Z → B≢B refl
                                                                     ; (S ∋op) → ∌op ∋op})

   _⊆_ : OpContext → OpContext → Set
   Δ ⊆ Δ' = ∀ {label : String} {A B : ValueType} 
            → (op : Operation label A B) 
            → Δ ∋-op op → Δ' ∋-op op

   _\'_ : OpContext → OpContext → OpContext
   ∅ \' Δ' = ∅
   (Δ ∷ op) \' Δ' with Δ' ∋-op? op
   ... | yes _ = Δ \' Δ'
   ... | no  _ = (Δ \' Δ') ∷ op

   _≟-op′_  : ∀ {label label′ A A′ B B′}
            → (op : Operation label A B)
            → (op' : Operation label′ A′ B′)
            → Dec (label ≡ label′ × A ≡ A′ × B ≡ B′)
   (label ⦂ A —→ B) ≟-op′ (label′ ⦂ A′ —→ B′) with label ≟ label′ | A ≟-v A′ | B ≟-v B′
   ... | yes refl        | yes refl  | yes refl  = yes ⟨ refl ,′ ⟨ refl ,′ refl ⟩ ⟩
   ... | no label≢label′ | _         | _         = no (λ{ ⟨ label≡label′ , _ ⟩ → label≢label′ label≡label′})
   ... | _               | no A≢A′   | _         = no (λ{ ⟨ _ , ⟨ A≡A′ , _ ⟩ ⟩ → A≢A′ A≡A′})
   ... | _               | _         | no B≢B′   = no (λ{ ⟨ _ , ⟨ _ , B≡B′ ⟩ ⟩ → B≢B′ B≡B′})

   _≟-op_   : ∀ {label A B}
            → (op : Operation label A B)
            → (op' : Operation label A B)
            → Dec (op ≡ op')
   (label ⦂ A —→ B) ≟-op (label' ⦂ A' —→ B') with label ≟ label' | A ≟-v A' | B ≟-v B' 
   ... | yes refl        | yes refl  | yes refl  = yes refl
   ... | no label≢label' | _         | _         = no λ  {refl → label≢label' refl}
   ... | _               | no A≢A'   | _         = no λ  {refl → A≢A' refl}
   ... | _               | _         | no B≢B'   = no λ  {refl → B≢B' refl}
  