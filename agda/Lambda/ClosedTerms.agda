
module Lambda.ClosedTerms where

open import Data.Empty
open import Data.Nat
open import Relation.Binary hiding (nonEmpty)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

open import Lambda.Core

data Closed′ (n : ℕ) : Term → Set where
  tvar-Closed′ : ∀ {v} → v < n → Closed′ n (tvar v)
  tapp-Closed′ : ∀ {t₁ t₂} → Closed′ n t₁ → Closed′ n t₂ → Closed′ n (tapp t₁ t₂)
  tabs-Closed′ : ∀ {t} → Closed′ (suc n) t → Closed′ n (tabs t)

Closed : Term → Set
Closed t = Closed′ 0 t

<-irreflexive : ∀ n → ¬ (n < n)
<-irreflexive 0 ()
<-irreflexive (suc n) ssn≤sn = <-irreflexive n (≤-pred ssn≤sn)

<⇒≢ : ∀ n m → n < m → n ≢ m
<⇒≢ n m n<m n≡m rewrite sym n≡m = <-irreflexive n n<m

closed′-subst : ∀ {n} t s v → Closed′ n t → n ≤ v → t [ v ≔ s ] ≡ t
closed′-subst (tvar x) s v (tvar-Closed′ x<n) n≤v with v ≟ x
... | yes v≡x = ⊥-elim (<⇒≢ x v (≤-trans x<n n≤v) (sym v≡x))
  where open DecTotalOrder decTotalOrder renaming (trans to ≤-trans)
... | no  _   = refl
closed′-subst (tapp t₁ t₂) s v (tapp-Closed′ t₁-closed′ t₂-closed′) n≤v = cong₂ tapp (closed′-subst t₁ s v t₁-closed′ n≤v) (closed′-subst t₂ s v t₂-closed′ n≤v)
closed′-subst (tabs t) s v (tabs-Closed′ t-closed′) n≤v = cong tabs (closed′-subst t (shift 1 0 s) (suc v) t-closed′ (s≤s n≤v))

closed-subst : ∀ t s v → Closed t → t [ v ≔ s ] ≡ t
closed-subst t s v closed = closed′-subst t s v closed z≤n

closed′-shift : ∀ {n} t d c → Closed′ n t → n ≤ c → shift d c t ≡ t
closed′-shift (tvar x) d c (tvar-Closed′ x<n) n≤c with c ≤? x
... | yes c≤x = ⊥-elim (<-irreflexive x (≤-trans x<n (≤-trans n≤c c≤x)))
  where open DecTotalOrder decTotalOrder renaming (trans to ≤-trans)
... | no  _   = refl
closed′-shift (tapp t₁ t₂) d c (tapp-Closed′ t₁-closed′ t₂-closed′) n≤c = cong₂ tapp (closed′-shift t₁ d c t₁-closed′ n≤c) (closed′-shift t₂ d c t₂-closed′ n≤c)
closed′-shift (tabs t) d c (tabs-Closed′ t-closed′) n≤c = cong tabs (closed′-shift t d (suc c) t-closed′ (s≤s n≤c))

closed-shift : ∀ t d c → Closed t → shift d c t ≡ t
closed-shift t d c closed = closed′-shift t d c closed z≤n

closed′-unshift : ∀ {n} t d c → Closed′ n t → n ≤ c → unshift d c t ≡ t
closed′-unshift (tvar x) d c (tvar-Closed′ x<n) n≤c with c ≤? x
... | yes c≤x = ⊥-elim (<-irreflexive x (≤-trans x<n (≤-trans n≤c c≤x)))
  where open DecTotalOrder decTotalOrder renaming (trans to ≤-trans)
... | no  _   = refl
closed′-unshift (tapp t₁ t₂) d c (tapp-Closed′ t₁-closed′ t₂-closed′) n≤c = cong₂ tapp (closed′-unshift t₁ d c t₁-closed′ n≤c) (closed′-unshift t₂ d c t₂-closed′ n≤c)
closed′-unshift (tabs t) d c (tabs-Closed′ t-closed′) n≤c = cong tabs (closed′-unshift t d (suc c) t-closed′ (s≤s n≤c))

closed-unshift : ∀ t d c → Closed t → unshift d c t ≡ t
closed-unshift t d c closed = closed′-unshift t d c closed z≤n