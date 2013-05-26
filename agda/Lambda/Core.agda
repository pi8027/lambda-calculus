
module Lambda.Core where

import Level
open import Function
open import Data.Nat
open import Data.Star
open import Data.Star.Properties
open import Relation.Nullary
open import Relation.Binary

data Term : Set where
  tvar : ℕ → Term
  tapp : Term → Term → Term
  tabs : Term → Term

shift : ℕ → ℕ → Term → Term
shift d c (tvar n) with c ≤? n
...| yes p = tvar (n + d)
...| no p = tvar n
shift d c (tapp t1 t2) = tapp (shift d c t1) (shift d c t2)
shift d c (tabs t) = tabs $ shift d (suc c) t

unshift : ℕ → ℕ → Term → Term
unshift d c (tvar n) with c ≤? n
...| yes p = tvar (n ∸ d)
...| no p = tvar n
unshift d c (tapp t1 t2) = tapp (unshift d c t1) (unshift d c t2)
unshift d c (tabs t) = tabs $ unshift d (suc c) t

nshift : ℕ → Term → Term
nshift 0 t = t
nshift (suc n) t = shift 1 0 $ nshift n t

_[_≔_] : Term → ℕ → Term → Term
tvar n' [ n ≔ t ] with n ≟ n'
...| yes p = t
...| no p = tvar n'
tapp t1 t2 [ n ≔ t ] = tapp (t1 [ n ≔ t ]) (t2 [ n ≔ t ])
tabs t1 [ n ≔ t ] = tabs $ t1 [ suc n ≔ shift 1 0 t ]

data _→β_ : Rel Term Level.zero where
  →βbeta : ∀ {t1 t2} → tapp (tabs t1) t2 →β unshift 1 0 (t1 [ 0 ≔ shift 1 0 t2 ])
  →βappl : ∀ {t1 t1' t2} → t1 →β t1' → tapp t1 t2 →β tapp t1' t2
  →βappr : ∀ {t1 t2 t2'} → t2 →β t2' → tapp t1 t2 →β tapp t1 t2'
  →βabs  : ∀ {t t'} → t →β t' → tabs t →β tabs t'

_→β⋆_ : Rel Term Level.zero
_→β⋆_ = Star _→β_

→β⋆appl : ∀ {t1 t1' t2} → t1 →β⋆ t1' → tapp t1 t2 →β⋆ tapp t1' t2
→β⋆appl ε = ε
→β⋆appl (r1 ◅ r2) = →βappl r1 ◅ →β⋆appl r2

→β⋆appr : ∀ {t1 t2 t2'} → t2 →β⋆ t2' → tapp t1 t2 →β⋆ tapp t1 t2'
→β⋆appr ε = ε
→β⋆appr (r1 ◅ r2) = →βappr r1 ◅ →β⋆appr r2

→β⋆abs : ∀ {t t'} → t →β⋆ t' → tabs t →β⋆ tabs t'
→β⋆abs ε = ε
→β⋆abs (r1 ◅ r2) = →βabs r1 ◅ →β⋆abs r2

data _→βP_ : Rel Term Level.zero where
  →βPvar : ∀ {n} → tvar n →βP tvar n
  →βPapp : ∀ {t1 t1' t2 t2'} → t1 →βP t1' → t2 →βP t2' → tapp t1 t2 →βP tapp t1' t2'
  →βPabs : ∀ {t t'} → t →βP t' → tabs t →βP tabs t'
  →βPbeta : ∀ {t1 t1' t2 t2'} → t1 →βP t1' → t2 →βP t2' →
            tapp (tabs t1) t2 →βP unshift 1 0 (t1' [ 0 ≔ shift 1 0 t2' ])

_* : Term → Term
tvar n * = tvar n
tapp (tabs t1) t2 * = unshift 1 0 (t1 * [ 0 ≔ shift 1 0 (t2 *) ])
tapp t1 t2 * = tapp (t1 *) (t2 *)
tabs t * = tabs (t *)

module →β⋆-Reasoning where
  open StarReasoning (_→β_) public renaming (_⟶⋆⟨_⟩_ to _→β⋆⟨_⟩_)

  infixr 2 _↘⟨_⟩_↙_

  _↘⟨_⟩_↙_ : ∀ {a} {b} {z} → (f : Term → Term) → (∀ {x} {y} → x →β⋆ y → f x →β⋆ f y) → a →β⋆ b → f b IsRelatedTo z → f a IsRelatedTo z
  f ↘⟨ congr ⟩ a→β⋆b ↙ (relTo fb→β⋆z) = relTo (congr a→β⋆b ◅◅ fb→β⋆z)