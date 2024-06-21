open import Data.Product using (Σ-syntax; ∃-syntax; _×_) renaming (_,′_ to ⟨_,_⟩; _,_ to ⟨_,'_⟩)
open import Data.Fin using (zero; suc)

open import effect.Lang

open import Agda.Builtin.String using (String)

module effect.Playground where

    read : Operation "read" _ _
    read = "read" ⦂ unit —→ str 

    print : Operation "print" _ _
    print = "print" ⦂ str —→ unit

    Σ : OpContext
    Σ = ∅ ∷ read ∷ print
    
    Δ : OpContext
    Δ = Σ
    
    printFullName   : Σ ⨟ ∅ ⊢c unit ! Δ
    printFullName   = 
        opCall[ print ] `· (`s "What is your forename?") ⨟ 
        `do←— opCall[ read ] `· `unit 
         `in (opCall[ print ] `· (`s "What is your surname?") ⨟ 
                   `do←— opCall[ read ] `· `unit
                    `in (   opCall[ print ] `· (# 1) ⨟ 
                            opCall[ print ] `· (# 0)))

    _ : Σ ⨟ ∅ ⊢c str ! Δ
    _ = opCall[ read ] `· `unit

    _ : Σ ⨟ ∅ ⊢c unit ! Δ
    _ = `do←— (opCall[ read ] `· `unit) 
        `in (opCall[ print ] `· (` Z))

    _ : Σ ⨟ ∅ ⊢c bool ! ∅
    _ = `return `true

    _ : Σ ⨟ ∅ ⊢c bool ! ∅
    _ = `return `false

    _ : Σ ⨟ ∅ ⊢c str ! ∅
    _ = `return (`s "hello")

    _ : Σ ⨟ ∅ ⊢v str —→ unit ! ∅
    _ = `fun (`return `unit)

    _ : Σ ⨟ (∅ ∷ str ∷ unit ∷ int) ⊢v str —→ unit ! ∅
    _ = `fun (`return (# 2))

    --------------- TEST: handler
    

    Δ' : OpContext
    Δ' = ∅ ∷ read

    _ : Σ ⨟ ∅ ⊢v str ! Δ' ⟹ str ! ∅
    _ = `handler
            handler[ 
                `return (# 0) , 
                ∅ ∷ [ read ]↦ `return (`s "data") 
            ]
            λ{ _ () }

  