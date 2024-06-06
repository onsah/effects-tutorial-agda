open import effect.Lang
open import effect.Lang using (module SyntaxSugar)
-- open import Data.Vec using (Vec; []; _∷_; lookup)
open import Data.List using (List; []; _∷_)
open import Data.Product using (Σ-syntax; ∃-syntax; _×_) renaming (_,′_ to ⟨_,_⟩; _,_ to ⟨_,'_⟩)
open import Data.Fin using (zero; suc)
open SyntaxSugar

open import Agda.Builtin.String using (String)

module effect.Playground where
    Δ : OpLabelContext
    Δ = ∅ₑₗ ,ₑₗ "read" ,ₑₗ "print"

    read : Operation "read" _ _
    read = "read" ⦂ unit —→ str 

    print : Operation "print" _ _
    print = "print" ⦂ str —→ unit

    Σ : OpContext
    Σ = ∅ₑ ,ₑ read ,ₑ print

    -- TODO: Try only using one effect
    
    {- _ : Σ ⨟ ∅ ⊢c str ! Δ
    _ = `op Sₑₗ (λ ()) Zₑₗ ∧ Sₑ Zₑ [ `unit ]⇒ 
            `return (` Z)

    _ : Σ ⨟ ∅ ⊢c str ! Δ
    _ = opCall[ (Sₑₗ (λ ()) Zₑₗ) ∧ (Sₑ Zₑ) ] `· `unit -}

    _ : Σ ⨟ ∅ ⊢c str ! Δ
    _ = opCall[ read ] `· `unit

    _ : Σ ⨟ ∅ ⊢c unit ! Δ
    _ = `do←— (opCall[ read ] `· `unit) 
        `in (weakenᵥ (opCall[ print ]) `· (` Z))

    _ : Σ ⨟ ∅ ⊢c bool ! ∅ₑₗ
    _ = `return `true

    _ : Σ ⨟ ∅ ⊢c bool ! ∅ₑₗ
    _ = `return `false

    _ : Σ ⨟ ∅ ⊢c str ! ∅ₑₗ
    _ = `return (`s "hello")

    _ : Σ ⨟ ∅ ⊢v str —→ unit ! ∅ₑₗ
    _ = `fun (`return `unit)

    _ : Σ ⨟ (∅ , str , unit , int) ⊢v str —→ unit ! ∅ₑₗ
    _ = `fun (`return (# 2))

    --------------- TEST: handler

    Δ' : OpLabelContext
    Δ' = ∅ₑₗ ,ₑₗ "read"

    fakeop : Operation "fake" _ _
    fakeop = "fake" ⦂ int —→ int

    _ : Σ ⨟ ∅ ⊢v str ! Δ' ⟹ str ! ∅ₑₗ
    _ = `handler
            (record { 
                return = `return (# 0) ; 
                effects = ∅ ,[ 
                    read ⇒ `return (`s "data") 
                ]
            })
            λ{ _ () }
    {- _ = `handler {opLabels = "read" ∷ []} 
            (`return (` Z)) 
            (λ{ zero → ⟨ unit ,' ⟨ str ,' 
                ⟨ read ,' ⟨ (Sₑ Zₑ) ,' 
                    (` Z) `· `s "data" ⟩ ⟩ ⟩ ⟩}) 
            (subset λ{_ ()}) -}

  