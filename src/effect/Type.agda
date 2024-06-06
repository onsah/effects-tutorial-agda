open import Data.String using (String)
open import Data.String.Properties using (_≟_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

module effect.Type where
    
    infix  4 _∋ₑₗ_
    infixl 5 _,ₑₗ_
    infix 6 _!_
    infixr 5 _—→_
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

    contains : (Δ : OpLabelContext) → (oL : String) → Dec (Δ ∋ₑₗ oL)
    contains ∅ₑₗ oL = no λ()
    contains (Δ ,ₑₗ oL') oL with oL ≟ oL'
    ... | yes refl = yes Zₑₗ
    ... | no ¬Z with contains Δ oL
    ...   | yes ∋oL = yes (Sₑₗ ¬Z ∋oL)
    ...   | no ¬S = no (λ{ Zₑₗ → ¬Z refl
                        ; (Sₑₗ _ ∋oL) → ¬S ∋oL}) 

    _⊆_ : OpLabelContext → OpLabelContext → Set
    Δ ⊆ Δ' = ∀ (s : String) → Δ ∋ₑₗ s → Δ' ∋ₑₗ s

    _\'_ : OpLabelContext → OpLabelContext → OpLabelContext
    ∅ₑₗ \' Δ' = ∅ₑₗ
    (Δ ,ₑₗ x) \' Δ' with contains Δ' x
    ... | yes _ = Δ \' Δ'
    ... | no _ = (Δ \' Δ') ,ₑₗ x

    -- TODO: Convert it to record
    data Operation : String → ValueType → ValueType → Set

    data Operation where
        _⦂_—→_  : (label : String) → (A : ValueType) → (B : ValueType) 
                → Operation label A B

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
