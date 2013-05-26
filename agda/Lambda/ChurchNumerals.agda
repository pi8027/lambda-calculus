
module Lambda.ChurchNumerals where

open import Function
open import Data.Nat
open import Data.Star
open import Data.Star.Properties
open import Relation.Binary.PropositionalEquality

open import Lambda.Core
open import Lambda.ClosedTerms
open import Lambda.Properties

open →β⋆-Reasoning

iter-tapp : ℕ → Term → Term → Term
iter-tapp 0       f b = b
iter-tapp (suc n) f b = tapp f (iter-tapp n f b)

iter-tapp-+ : ∀ n m f b → iter-tapp n f (iter-tapp m f b) ≡ iter-tapp (n + m) f b
iter-tapp-+ 0       m f b = refl
iter-tapp-+ (suc n) m f b = cong (tapp f) (iter-tapp-+ n m f b)

iter-tapp-closed : ∀ n f b l → Closed′ l f → Closed′ l b → Closed′ l (iter-tapp n f b)
iter-tapp-closed 0       f b l f-closed′ b-closed′ = b-closed′
iter-tapp-closed (suc n) f b l f-closed′ b-closed′ = ctapp f-closed′ (iter-tapp-closed n f b l f-closed′ b-closed′)

iter-tapp-subst : ∀ n f b v s → iter-tapp n f b [ v ≔ s ] ≡ iter-tapp n (f [ v ≔ s ]) (b [ v ≔ s ])
iter-tapp-subst 0       f b v s = refl
iter-tapp-subst (suc n) f b v s = cong (tapp (f [ v ≔ s ])) (iter-tapp-subst n f b v s)

iter-tapp-shift : ∀ n f b c d → shift c d (iter-tapp n f b) ≡ iter-tapp n (shift c d f) (shift c d b)
iter-tapp-shift 0       f b c d = refl
iter-tapp-shift (suc n) f b c d = cong (tapp (shift c d f)) (iter-tapp-shift n f b c d)

iter-tapp-unshift : ∀ n f b c d → unshift c d (iter-tapp n f b) ≡ iter-tapp n (unshift c d f) (unshift c d b)
iter-tapp-unshift 0       f b c d = refl
iter-tapp-unshift (suc n) f b c d = cong (tapp (unshift c d f)) (iter-tapp-unshift n f b c d)

-- (λ s. λ z. s (s (... (s z)))) where the number of applications of `s` is given by the first parameter
church : ℕ → Term
church n = tabs (tabs (iter-tapp n (tvar 1) (tvar 0)))

church-closed : ∀ n → Closed (church n)
church-closed n = ctabs (ctabs (iter-tapp-closed n (tvar 1) (tvar 0) 2 (ctvar (s≤s (s≤s z≤n))) (ctvar (s≤s z≤n))))

-- (λ a b s z. a s (b s z))
church-+ : Term
church-+ = tabs (tabs (tabs (tabs (tapp (tapp (tvar 3) (tvar 1))
                                        (tapp (tapp (tvar 2) (tvar 1)) (tvar 0))))))

church-+-correct : ∀ n m → tapp (tapp church-+ (church n)) (church m) →β⋆ church (n + m)
church-+-correct n m =
  begin
    tapp (tapp church-+ (church n)) (church m)
      →β⋆⟨ return (→βappl (→βbeta-closed (church-closed n))) ⟩
    tapp (tabs (tabs (tabs (tapp (tapp (church n) (tvar 1)) _)))) (church m)
      →β⋆⟨ return (→βbeta-closed (church-closed m)) ⟩
    (tabs ∘ tabs)
      ↘⟨ →β⋆abs ∘ →β⋆abs ⟩
        begin
          tapp (tapp _ (tvar 1)) (tapp (tapp (church m) _) _)
            ≡⟨ cong₂ tapp (cong₂ tapp (closed-beta-closed (church n) 2 (church m) (church-closed n)) refl) refl ⟩
          tapp (tapp (church n) (tvar 1)) (tapp (tapp (church m) (tvar 1)) (tvar 0))
            →β⋆⟨ →βappl →βbeta ◅ →βappr (→βappl →βbeta) ◅ ε ⟩
          tapp (tabs _) (tapp (tabs _) (tvar 0))
            ≡⟨ (let a = λ k → cong tabs (trans (cong (unshift 1 1) (iter-tapp-subst k (tvar 1) (tvar 0) 1 (tvar 3))) (iter-tapp-unshift k (tvar 3) (tvar 0) 1 1)) in cong₂ tapp (a n) (cong₂ tapp (a m) refl)) ⟩
          tapp (tabs (iter-tapp n (tvar 2) (tvar 0))) (tapp (tabs (iter-tapp m (tvar 2) (tvar 0))) (tvar 0))
            →β⋆⟨ return (→βappr →βbeta) ⟩
          tapp (tabs (iter-tapp n (tvar 2) (tvar 0))) _
            ≡⟨ cong (tapp _) (trans (cong (unshift 1 0) (iter-tapp-subst m (tvar 2) (tvar 0) 0 (tvar 1))) (iter-tapp-unshift m (tvar 2) (tvar 1) 1 0)) ⟩
          tapp (tabs (iter-tapp n (tvar 2) (tvar 0))) (iter-tapp m (tvar 1) (tvar 0))
            →β⋆⟨ return →βbeta ⟩
          _
           ≡⟨ trans (cong (unshift 1 0) (iter-tapp-subst n (tvar 2) (tvar 0) 0 (shift 1 0 (iter-tapp m (tvar 1) (tvar 0))))) (trans (iter-tapp-unshift n (tvar 2) (shift 1 0 (iter-tapp m (tvar 1) (tvar 0))) 1 0) (cong (iter-tapp n (tvar 1)) (trans (cong (unshift 1 0) (iter-tapp-shift m (tvar 1) (tvar 0) 1 0)) (iter-tapp-unshift m (tvar 2) (tvar 1) 1 0)))) ⟩
          iter-tapp n (tvar 1) (iter-tapp m (tvar 1) (tvar 0))
            ≡⟨ iter-tapp-+ n m (tvar 1) (tvar 0) ⟩
          iter-tapp (n + m) (tvar 1) (tvar 0)
        ∎
      ↙
    tabs (tabs (iter-tapp (n + m) (tvar 1) (tvar 0)))
      ≡⟨ refl ⟩
    church (n + m)
  ∎