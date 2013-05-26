
module Lambda.ChurchNumerals where

open import Data.Nat
open import Data.Star
open import Data.Star.Properties
open import Relation.Binary.PropositionalEquality

open import Lambda.Core
open import Lambda.ClosedTerms
open import Lambda.Properties

open →β⋆-Reasoning renaming (_≡⟨_⟩_ to _≅⟨_⟩_; begin_ to βbegin_; _∎ to _β∎)

iter-tapp : ℕ → Term → Term → Term
iter-tapp 0       f b = b
iter-tapp (suc n) f b = tapp f (iter-tapp n f b)

iter-tapp-+ : ∀ n m f b → iter-tapp n f (iter-tapp m f b) ≡ iter-tapp (n + m) f b
iter-tapp-+ 0       m f b = refl
iter-tapp-+ (suc n) m f b = cong (tapp f) (iter-tapp-+ n m f b)

iter-tapp-closed : ∀ n f b l → Closed′ l f → Closed′ l b → Closed′ l (iter-tapp n f b)
iter-tapp-closed 0       f b l f-closed′ b-closed′ = b-closed′
iter-tapp-closed (suc n) f b l f-closed′ b-closed′ = tapp-Closed′ f-closed′ (iter-tapp-closed n f b l f-closed′ b-closed′)

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
church-closed n = tabs-Closed′ (tabs-Closed′ (iter-tapp-closed n (tvar 1) (tvar 0) 2 (tvar-Closed′ (s≤s (s≤s z≤n))) (tvar-Closed′ (s≤s z≤n))))

-- (λ a b s z. a s (b s z))
church-+ : Term
church-+ = tabs (tabs (tabs (tabs (tapp (tapp (tvar 3) (tvar 1))
                                        (tapp (tapp (tvar 2) (tvar 1)) (tvar 0))))))

church-+-correct : ∀ n m → tapp (tapp church-+ (church n)) (church m) →β* church (n + m)
church-+-correct n m =
  βbegin
    tapp (tapp church-+ (church n)) (church m)
      →β⋆⟨ return (→βappl →βbeta) ⟩
    tapp (tabs (tabs (tabs (tapp (tapp (unshift 1 3 (shift 1 0 (shift 1 0 (shift 1 0 (shift 1 0 (church n)))))) (tvar 1)) _)))) (church m)
      ≅⟨ cong₂ tapp (cong tabs (cong tabs (cong tabs (cong₂ tapp (cong₂ tapp eq₁ refl) refl)))) refl ⟩
    tapp (tabs (tabs (tabs (tapp (tapp (church n) (tvar 1)) _)))) (church m)
      →β⋆⟨ return →βbeta ⟩
    tabs (tabs (tapp (tapp (unshift 1 (suc (suc 0)) (church n [ suc (suc 0) ≔ shift 1 0 (shift 1 0 (shift 1 0 (church m))) ])) (tvar 1))
                     (tapp (tapp (unshift 1 2 (shift 1 0 (shift 1 0 (shift 1 0 (church m))))) _) _)))
      ≅⟨ cong tabs (cong tabs (cong₂ tapp (cong₂ tapp eq₂ refl) (cong₂ tapp (cong₂ tapp eq₃ refl) refl))) ⟩
    tabs (tabs (tapp (tapp (church n) (tvar 1)) (tapp (tapp (church m) (tvar 1)) (tvar 0))))
      →β⋆⟨ →βabs (→βabs (→βappl →βbeta)) ◅ (→βabs (→βabs (→βappr (→βappl →βbeta))) ◅ ε) ⟩
    tabs (tabs (tapp (tabs _) (tapp (tabs _) (tvar 0))))
      ≅⟨ cong tabs (cong tabs (let a = λ k → cong tabs (trans (cong (unshift 1 1) (iter-tapp-subst k (tvar 1) (tvar 0) 1 (tvar 3))) (iter-tapp-unshift k (tvar 3) (tvar 0) 1 1)) in cong₂ tapp (a n) (cong₂ tapp (a m) refl))) ⟩
    tabs (tabs (tapp (tabs (iter-tapp n (tvar 2) (tvar 0))) (tapp (tabs (iter-tapp m (tvar 2) (tvar 0))) (tvar 0))))
      →β⋆⟨ return (→βabs (→βabs (→βappr →βbeta))) ⟩
    tabs (tabs (tapp (tabs (iter-tapp n (tvar 2) (tvar 0))) _))
      ≅⟨ cong tabs (cong tabs (cong (tapp _) (trans (cong (unshift 1 0) (iter-tapp-subst m (tvar 2) (tvar 0) 0 (tvar 1))) (iter-tapp-unshift m (tvar 2) (tvar 1) 1 0)))) ⟩
    tabs (tabs (tapp (tabs (iter-tapp n (tvar 2) (tvar 0))) (iter-tapp m (tvar 1) (tvar 0))))
      →β⋆⟨ return (→βabs (→βabs →βbeta)) ⟩
    tabs (tabs _)
      ≅⟨ cong tabs (cong tabs (trans (cong (unshift 1 0) (iter-tapp-subst n (tvar 2) (tvar 0) 0 (shift 1 0 (iter-tapp m (tvar 1) (tvar 0))))) (trans (iter-tapp-unshift n (tvar 2) (shift 1 0 (iter-tapp m (tvar 1) (tvar 0))) 1 0) (cong (iter-tapp n (tvar 1)) (trans (cong (unshift 1 0) (iter-tapp-shift m (tvar 1) (tvar 0) 1 0)) (iter-tapp-unshift m (tvar 2) (tvar 1) 1 0)))))) ⟩
    tabs (tabs (iter-tapp n (tvar 1) (iter-tapp m (tvar 1) (tvar 0))))
      ≅⟨ cong tabs (cong tabs (iter-tapp-+ n m (tvar 1) (tvar 0))) ⟩
    tabs (tabs (iter-tapp (n + m) (tvar 1) (tvar 0)))
      ≅⟨ refl ⟩
    church (n + m)
  β∎
  where open ≡-Reasoning hiding (_≅⟨_⟩_)
        eq₁ = begin
            (unshift 1 3 (shift 1 0 (shift 1 0 (shift 1 0 (shift 1 0 (church n))))))
              ≡⟨ cong (unshift 1 3) (trans (shiftAdd 1 1 0 (shift 1 0 (shift 1 0 (church n)))) (trans (shiftAdd 2 1 0 (shift 1 0 (church n))) (shiftAdd 3 1 0 (church n)))) ⟩
            unshift 1 3 (shift 4 0 (church n))
              ≡⟨ cong (unshift 1 3) (closed-shift (church n) 4 0 (church-closed n)) ⟩
            unshift 1 3 (church n)
              ≡⟨ closed-unshift (church n) 1 3 (church-closed n) ⟩
            church n
          ∎
        eq₂ = (trans (cong (unshift 1 2) (closed-subst (church n) (shift 1 0 (shift 1 0 (shift 1 0 (church m)))) 2 (church-closed n))) (closed-unshift (church n) 1 2 (church-closed n)))
        eq₃ = begin
            unshift 1 2 (shift 1 0 (shift 1 0 (shift 1 0 (church m)))) ≡⟨ cong (unshift 1 2) (trans (shiftAdd 1 1 0 (shift 1 0 (church m))) (shiftAdd 2 1 0 (church m))) ⟩
            unshift 1 2 (shift 3 0 (church m))                         ≡⟨ cong (unshift 1 2) (closed-shift (church m) 3 0 (church-closed m)) ⟩
            unshift 1 2 (church m)                                     ≡⟨ closed-unshift (church m) 1 2 (church-closed m) ⟩
            church m
          ∎