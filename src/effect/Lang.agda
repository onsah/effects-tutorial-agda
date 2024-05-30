{-# OPTIONS --allow-unsolved-metas #-} 

open import Agda.Builtin.String using (String)
open import Agda.Builtin.Maybe using (Maybe)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Vec using (Vec; []; _∷_; lookup)
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.Bool using (Bool)
open import Data.Product using (Σ-syntax; ∃-syntax; _×_) renaming (_,′_ to ⟨_,_⟩)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (True)

module effect.Lang where

    infix 3 _⨟_⊢v_
    infix 3 _⨟_⊢c_
    infix  4 _∋_
    infix  4 _∋ₑ_
    infixl 5 _,_
    infixl 5 _,ₑ_

    case_of_ : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
    case x of f = f x

    module Type where
      open import Data.String.Properties using (_≟_)
      
      infix  4 _∋ₑₗ_
      infixl 5 _,ₑₗ_
      infix 6 _!_
      infix 5 _—→_
      infix 5 _⟹_
      infix 5 _⦂_—→_

      data ValueType : Set
      data ComputationType : Set
      data OpLabelContext : Set
    
      data ValueType where
        bool : ValueType
        str  : ValueType
        int  : ValueType
        unit : ValueType
        void : ValueType
        _—→_ : ValueType → ComputationType → ValueType
        _⟹_ : ComputationType → ComputationType → ValueType

      data ComputationType where
          -- Operation list is an overappromixation of what the computation actually uses.
          _!_ : ValueType → OpLabelContext → ComputationType

      data OpLabelContext where
        ∅ₑₗ : OpLabelContext
        _,ₑₗ_ : OpLabelContext → String → OpLabelContext

      _≟-v_ : (A : ValueType)
            → (B : ValueType)
            → Dec (A ≡ B)
      _≟-c_ : (A : ComputationType)
            → (B : ComputationType)
            → Dec (A ≡ B)
      _≟-Δ_ : (Δ₁ : OpLabelContext)
            → (Δ₂ : OpLabelContext)
            → Dec (Δ₁ ≡ Δ₂)
      
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

      ∅ₑₗ ≟-Δ ∅ₑₗ = yes refl
      ∅ₑₗ ≟-Δ (Δ₂ ,ₑₗ x) = no (λ())
      (Δ₁ ,ₑₗ x) ≟-Δ ∅ₑₗ = no (λ())
      (Δ₁ ,ₑₗ x₁) ≟-Δ (Δ₂ ,ₑₗ x₂)  with x₁ ≟ x₂ 
      ... | no x₁≢x₂ = no λ { refl → x₁≢x₂ refl}
      ... | yes refl with Δ₁ ≟-Δ Δ₂
      ...   | no Δ₁≢Δ₂ = no λ { refl → Δ₁≢Δ₂ refl}
      ...   | yes refl = yes refl

      data _∋ₑₗ_ : OpLabelContext → String → Set 
        where
        Zₑₗ : {Δ : OpLabelContext} {oL : String}
            → Δ ,ₑₗ oL ∋ₑₗ oL
        
        Sₑₗ  : {Δ : OpLabelContext}
              {oL oL' : String}
              → ¬ (oL ≡ oL')
              → Δ ∋ₑₗ oL
              → Δ ,ₑₗ oL' ∋ₑₗ oL

      -- This is used for proof by reflection
      -- So that we can just specify the label of the effect and the proof is found automatically
      _∋ₑₗ?_  : (Δ : OpLabelContext)
              → (opLabel : String)
              → Dec (Δ ∋ₑₗ opLabel)
      ∅ₑₗ ∋ₑₗ? opLabel = no (λ())
      (Δ ,ₑₗ x) ∋ₑₗ? opLabel with opLabel ≟ x
      ... | yes refl = yes Zₑₗ
      ... | no opLabel≢x with Δ ∋ₑₗ? opLabel
      ...   | yes ∋opLabel = yes (Sₑₗ opLabel≢x ∋opLabel)
      ...   | no ¬∋opLabel = no (λ{ Zₑₗ → opLabel≢x refl
                                  ; (Sₑₗ _ ∋opLabel) → ¬∋opLabel ∋opLabel})

      module OpLabelContextOps where
        open import Data.String.Properties using (_≟_)

        contains : (Δ : OpLabelContext) → (oL : String) → Dec (Δ ∋ₑₗ oL)
        contains ∅ₑₗ oL = no λ()
        contains (Δ ,ₑₗ oL') oL with oL ≟ oL'
        ... | yes refl = yes Zₑₗ
        ... | no ¬Z with contains Δ oL
        ...   | yes ∋oL = yes (Sₑₗ ¬Z ∋oL)
        ...   | no ¬S = no (λ{ Zₑₗ → ¬Z refl
                            ; (Sₑₗ _ ∋oL) → ¬S ∋oL}) 

        -- TODO: How to implement?
        data _⊆_ : OpLabelContext → OpLabelContext → Set where
          subset  : {Δ Δ' : OpLabelContext}
                  → (∀ (s : String) → Δ ∋ₑₗ s → Δ' ∋ₑₗ s)
                  → Δ ⊆ Δ'

        fromVec : {n : ℕ}
                → Vec String n
                → OpLabelContext
        fromVec [] = ∅ₑₗ
        fromVec (oL ∷ oLs) = (fromVec oLs) ,ₑₗ oL

        _\'_ : OpLabelContext → OpLabelContext → OpLabelContext
        ∅ₑₗ \' Δ' = ∅ₑₗ
        (Δ ,ₑₗ x) \' Δ' with contains Δ' x
        ... | yes _ = Δ \' Δ'
        ... | no _ = (Δ \' Δ') ,ₑₗ x
      
      open OpLabelContextOps public
    
      data Operation : String → ValueType → ValueType → Set

      data Operation where
          _⦂_—→_  : (label : String) → (A : ValueType) → (B : ValueType) 
                  → Operation label A B

      module OperationOps where

        label : ∀ {label A B}
              → Operation label A B → String
        label (label ⦂ _ —→ _) = label

        _≟-op_  : ∀ {label A B}
                → (op : Operation label A B)
                → (op' : Operation label A B)
                → Dec (op ≡ op')
        (label ⦂ A —→ B) ≟-op (label' ⦂ A' —→ B') with label ≟ label' | A ≟-v A' | B ≟-v B' 
        ... | yes refl        | yes refl  | yes refl  = yes refl
        ... | no label≢label' | _         | _         = no λ  {refl → label≢label' refl}
        ... | _               | no A≢A'   | _         = no λ  {refl → A≢A' refl}
        ... | _               | _         | no B≢B'   = no λ  {refl → B≢B' refl}

    open Type public

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

    -- This is used for proof by reflection
    -- So that we can just specify the label of the effect and the proof is found automatically
    open import Data.String.Properties using (_≟_)
    open OperationOps

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

    -- Thought it's appropriate to have effect context as a parameterized type since it's not supposed to change.
    -- Term typing rules are mutually recursive
    -- Can use '⨟' as separater between context
    data _⨟_⊢v_ (Σ : OpContext) (Γ : Context) : ValueType → Set
    -- Hmm: Maybe we should also have OpContext
    data _⨟_⊢c_ (Σ : OpContext) (Γ : Context) : ComputationType → Set

    -- Value terms
    data _⨟_⊢v_ Σ Γ where

        `_ : {A : ValueType}
           → Γ ∋ A
           → Σ ⨟ Γ ⊢v A
        
        `true : Σ ⨟ Γ ⊢v bool

        `false : Σ ⨟ Γ ⊢v bool
          
        `unit : Σ ⨟ Γ ⊢v unit

        `s  : String
            → Σ ⨟ Γ ⊢v str

        `fun : {A B : ValueType} {Δ : OpLabelContext}
             → Σ ⨟ (Γ , A) ⊢c B ! Δ
             → Σ ⨟ Γ ⊢v A —→ B ! Δ

        `handler  : {Δ Δ' : OpLabelContext}
                    {n : ℕ} {A B : ValueType}
                    {opLabels : Vec String n}
                  -- TODO: data Handler
                  -- Return handler body
                  → Σ ⨟ Γ , A ⊢c B ! Δ'
                  -- Asserts that every effect handler body is well typed according to it's effect
                  -- Make it it's own definition
                  → (∀ (i : Fin n) → 
                      ∃[ Aᵢ ] ∃[ Bᵢ ] 
                        Σ[ op ∈ Operation (lookup opLabels i) Aᵢ Bᵢ ] 
                          Σ ∋ₑ op × 
                          (Σ ⨟ Γ , Aᵢ , (Bᵢ —→ B ! Δ') ⊢c B ! Δ'))
                  → (Δ \' (fromVec opLabels)) ⊆ Δ'
                  → Σ ⨟ Γ ⊢v A ! Δ ⟹ B ! Δ'

    data _⨟_⊢c_ Σ Γ where
        
        `return : {A : ValueType} {Δ : OpLabelContext}
                → Σ ⨟ Γ ⊢v A
                → Σ ⨟ Γ ⊢c A ! Δ

        -- Op rule
        `op_[_]⇒_ : {Δ : OpLabelContext} 
                      {A Aₒₚ Bₒₚ : ValueType}
                      {opLabel : String} 
                    → (op : Operation opLabel Aₒₚ Bₒₚ)
                    → {True (Δ ∋ₑₗ? opLabel)}
                    → {True (Σ ∋ₑ? op)}
                    → Σ ⨟ Γ ⊢v Aₒₚ
                    → Σ ⨟ Γ , Bₒₚ ⊢c A ! Δ
                    → Σ ⨟ Γ ⊢c A ! Δ

        `do←—_`in_  : {Δ : OpLabelContext} 
                      {A B : ValueType}
                    → Σ ⨟ Γ ⊢c A ! Δ
                    → Σ ⨟ Γ , A ⊢c B ! Δ
                    → Σ ⨟ Γ ⊢c B ! Δ

        _`·_ : {A : ValueType} {Aₑ : ComputationType}
             → Σ ⨟ Γ ⊢v A —→ Aₑ
             → Σ ⨟ Γ ⊢v A
             → Σ ⨟ Γ ⊢c Aₑ

        `if_then_else : {Aₑ : ComputationType}
                      → Σ ⨟ Γ ⊢v bool
                      → Σ ⨟ Γ ⊢c Aₑ
                      → Σ ⨟ Γ ⊢c Aₑ
                      → Σ ⨟ Γ ⊢c Aₑ

        `with_handle_ : {Δ Δ' : OpLabelContext}
                        {A B : ValueType}
                      → Σ ⨟ Γ ⊢v A ! Δ' ⟹ B ! Δ
                      → Σ ⨟ Γ ⊢c A ! Δ' 
                      → Σ ⨟ Γ ⊢c B ! Δ

    Rename : Context → Context → Set
    Rename Γ Δ = ∀ {A} → Γ ∋ A → Δ ∋ A

    ext : {Γ Δ : Context}
        → Rename Γ Δ
        → ∀ {B} → Rename (Γ , B) (Δ , B)
    ext ρ Z = Z
    ext ρ (S x) = S (ρ x)

    renameᵥ  : {Σ : OpContext} {Γ Δ : Context}
            → Rename Γ Δ
            → ∀ {A} → Σ ⨟ Γ ⊢v A → Σ ⨟ Δ ⊢v A

    renameₑ  : {Σ : OpContext} {Γ Δ : Context}
            → Rename Γ Δ
            → ∀ {A} → Σ ⨟ Γ ⊢c A → Σ ⨟ Δ ⊢c A

    renameᵥ ρ (` ∋x) = ` (ρ ∋x)
    renameᵥ ρ `true = `true
    renameᵥ ρ `false = `false
    renameᵥ ρ `unit = `unit
    renameᵥ ρ (`s s) = `s s
    renameᵥ ρ (`fun ⊢body) = `fun (renameₑ (ext ρ) ⊢body)
    renameᵥ ρ (`handler x x₁ x₂) = {!   !}
    
    renameₑ ρ (`return ⊢v) = `return (renameᵥ ρ ⊢v)
    renameₑ ρ (`op_[_]⇒_ op {∋ₑₗ?opLabel} {∋ₑ?op} ⊢arg ⊢body) = 
      `op_[_]⇒_ op {∋ₑₗ?opLabel} {∋ₑ?op} 
        (renameᵥ ρ ⊢arg) 
        (renameₑ (ext ρ) ⊢body)
    renameₑ ρ (`do←— ⊢var `in ⊢body) = 
      `do←— (renameₑ ρ ⊢var) `in (renameₑ (ext ρ) ⊢body)
    renameₑ ρ (⊢f `· ⊢g) = (renameᵥ ρ ⊢f) `· (renameᵥ ρ ⊢g)
    renameₑ ρ (`if ⊢cond then ⊢then else ⊢else) = 
      `if (renameᵥ ρ ⊢cond) then (renameₑ ρ ⊢then) else (renameₑ ρ ⊢else)
    renameₑ ρ (`with ⊢handler handle ⊢body) = 
      `with (renameᵥ ρ ⊢handler) handle (renameₑ ρ ⊢body)

    weakenᵥ : {Σ : OpContext}
              {Γ : Context} {A B : ValueType}
            → Σ ⨟ Γ ⊢v A
            → Σ ⨟ Γ , B ⊢v A
    weakenₑ : {Σ : OpContext} {Δ : OpLabelContext}
              {Γ : Context} {A B : ValueType}
            → Σ ⨟ Γ ⊢c A ! Δ
            → Σ ⨟ Γ , B ⊢c A ! Δ

    weakenᵥ ⊢v = renameᵥ (S_) ⊢v

    weakenₑ ⊢c = renameₑ (S_) ⊢c


    module SyntaxSugar where

      opCall[_] : {A B : ValueType}
                  {Σ : OpContext} {Δ : OpLabelContext}
                  {opLabel : String}
                → (op : Operation opLabel A B)
                → {True (Δ ∋ₑₗ? opLabel)}
                → {True (Σ ∋ₑ? op)}
                → Σ ⨟ ∅ ⊢v A —→ B ! Δ
      opCall[_] op {∋ₑₗ?opLabel} {∋ₑ?op} =
        `fun (`op_[_]⇒_ op {∋ₑₗ?opLabel} {∋ₑ?op} (` Z) (`return (` Z)))
              
    open SyntaxSugar    