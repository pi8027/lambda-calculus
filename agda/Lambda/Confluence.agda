
module Lambda.Confluence where

open import Function
open import Data.Product
open import Data.Nat
open import Data.Nat.Properties
open import Data.Star
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

open import Lambda.Core
open import Lambda.Properties

→β*appl : ∀ {t1 t1' t2} → t1 →β* t1' → tapp t1 t2 →β* tapp t1' t2
→β*appl ε = ε
→β*appl (r1 ◅ r2) = →βappl r1 ◅ →β*appl r2

→β*appr : ∀ {t1 t2 t2'} → t2 →β* t2' → tapp t1 t2 →β* tapp t1 t2'
→β*appr ε = ε
→β*appr (r1 ◅ r2) = →βappr r1 ◅ →β*appr r2

→β*abs : ∀ {t t'} → t →β* t' → tabs t →β* tabs t'
→β*abs ε = ε
→β*abs (r1 ◅ r2) = →βabs r1 ◅ →β*abs r2

parRefl : ∀ {t} → t →βP t
parRefl {tvar _} = →βPvar
parRefl {tapp _ _} = →βPapp parRefl parRefl
parRefl {tabs _} = →βPabs parRefl

→β⊂→βP : _→β_ ⇒ _→βP_
→β⊂→βP →βbeta = →βPbeta parRefl parRefl
→β⊂→βP (→βappl r) = →βPapp (→β⊂→βP r) parRefl
→β⊂→βP (→βappr r) = →βPapp parRefl (→β⊂→βP r)
→β⊂→βP (→βabs r) = →βPabs (→β⊂→βP r)

→βP⊂→β* : _→βP_ ⇒ _→β*_
→βP⊂→β* →βPvar = ε
→βP⊂→β* (→βPapp r1 r2) = →β*appl (→βP⊂→β* r1) ◅◅ →β*appr (→βP⊂→β* r2)
→βP⊂→β* (→βPabs r) = →β*abs (→βP⊂→β* r)
→βP⊂→β* (→βPbeta r1 r2) = →β*appl (→β*abs (→βP⊂→β* r1)) ◅◅ →β*appr (→βP⊂→β* r2) ◅◅ →βbeta ◅ ε

shiftConservation→β : ∀ {d c} → _→β_ ⇒ ((λ a b → a → b) on Shifted d c)
shiftConservation→β {d} {c} {tapp (tabs t1) t2} →βbeta (sapp (sabs s1) s2) =
  betaShifted2 s1 s2
shiftConservation→β (→βappl p) (sapp s1 s2) = sapp (shiftConservation→β p s1) s2
shiftConservation→β (→βappr p) (sapp s1 s2) = sapp s1 (shiftConservation→β p s2)
shiftConservation→β (→βabs p) (sabs s1) = sabs (shiftConservation→β p s1)

shiftConservation→β* : ∀ {d c} → _→β*_ ⇒ ((λ a b → a → b) on Shifted d c)
shiftConservation→β* ε s = s
shiftConservation→β* (p1 ◅ p2) s = shiftConservation→β* p2 (shiftConservation→β p1 s)

shiftConservation→βP : ∀ {d c t1 t2} → t1 →βP t2 → Shifted d c t1 → Shifted d c t2
shiftConservation→βP p s = shiftConservation→β* (→βP⊂→β* p) s

shiftLemma : ∀ {t t' d c} → t →βP t' → shift d c t →βP shift d c t'
shiftLemma →βPvar = parRefl
shiftLemma (→βPapp r1 r2) = →βPapp (shiftLemma r1) (shiftLemma r2)
shiftLemma (→βPabs r) = →βPabs (shiftLemma r)
shiftLemma {d = d} {c} (→βPbeta {t1} {t1'} {t2} {t2'} r1 r2) = r where
  open ≡-Reasoning
  eq : shift d c (unshift 1 0 (t1' [ 0 ≔ shift 1 0 t2' ])) ≡
       unshift 1 0 (shift d (suc c) t1' [ 0 ≔ shift 1 0 (shift d c t2') ])
  eq = begin
    shift d c (unshift 1 0 (t1' [ 0 ≔ shift 1 0 t2' ]))
      ≡⟨ shiftUnshiftSwap z≤n (betaShifted' 0 t1' t2') ⟩
    unshift 1 0 (shift d (c + 1) (t1' [ 0 ≔ shift 1 0 t2' ]))
      ≡⟨ cong (unshift 1 0) $ begin
        shift d (c + 1) (t1' [ 0 ≔ shift 1 0 t2' ])
          ≡⟨ cong (λ c → shift d c (t1' [ 0 ≔ shift 1 0 t2' ])) (+-comm c 1) ⟩
        shift d (suc c) (t1' [ 0 ≔ shift 1 0 t2' ])
          ≡⟨ shiftSubstSwap (m≤m+n 1 c) t1' (shift 1 0 t2') ⟩
        shift d (suc c) t1' [ 0 ≔ shift d (suc c) (shift 1 0 t2') ]
          ≡⟨ cong (λ t → shift d (suc c) t1' [ 0 ≔ t ]) $ begin
            shift d (suc c) (shift 1 0 t2')
              ≡⟨ cong (λ c → shift d c (shift 1 0 t2')) (+-comm 1 c) ⟩
            shift d (c + 1) (shift 1 0 t2')
              ≡⟨ sym (shiftShiftSwap 1 0 d c t2' z≤n) ⟩
            shift 1 0 (shift d c t2') ∎
          ⟩
        shift d (suc c) t1' [ 0 ≔ shift 1 0 (shift d c t2') ] ∎
      ⟩
    unshift 1 0 (shift d (suc c) t1' [ 0 ≔ shift 1 0 (shift d c t2') ]) ∎
  r : shift d c (tapp (tabs t1) t2) →βP
      shift d c (unshift 1 0 (t1' [ 0 ≔ shift 1 0 t2' ]))
  r rewrite eq = →βPbeta (shiftLemma r1) (shiftLemma r2)

unshiftLemma : ∀ {t t' d c} → t →βP t' → Shifted d c t → unshift d c t →βP unshift d c t'
unshiftLemma →βPvar _ = parRefl
unshiftLemma (→βPapp r1 r2) (sapp s1 s2) = →βPapp (unshiftLemma r1 s1) (unshiftLemma r2 s2)
unshiftLemma (→βPabs r) (sabs s) = →βPabs (unshiftLemma r s)
unshiftLemma {d = d} {c} (→βPbeta {t1} {t1'} {t2} {t2'} r1 r2) (sapp (sabs s1) s2) = r where
  open ≡-Reasoning
  s1' = shiftConservation→βP r1 s1
  s2' = shiftConservation→βP r2 s2
  eq : unshift d c (unshift 1 0 (t1' [ 0 ≔ shift 1 0 t2' ])) ≡
       unshift 1 0 (unshift d (suc c) t1' [ 0 ≔ shift 1 0 (unshift d c t2') ])
  eq = begin
    unshift d c (unshift 1 0 (t1' [ 0 ≔ shift 1 0 t2' ]))
      ≡⟨ unshiftUnshiftSwap z≤n (betaShifted' 0 t1' t2') (betaShifted2 s1' s2') ⟩
    unshift 1 0 (unshift d (c + 1) (t1' [ 0 ≔ shift 1 0 t2' ]))
      ≡⟨ cong (unshift 1 0) $ begin
        unshift d (c + 1) (t1' [ 0 ≔ shift 1 0 t2' ])
          ≡⟨ cong (λ c → unshift d c (t1' [ 0 ≔ shift 1 0 t2' ])) (+-comm c 1) ⟩
        unshift d (suc c) (t1' [ 0 ≔ shift 1 0 t2' ])
          ≡⟨ unshiftSubstSwap2 (s≤s z≤n) s1' (shiftShifted' z≤n s2') ⟩
        unshift d (suc c) t1' [ 0 ≔ unshift d (suc c) (shift 1 0 t2') ]
          ≡⟨ cong (λ t → unshift d (suc c) t1' [ 0 ≔ t ]) $ begin
            unshift d (suc c) (shift 1 0 t2')
              ≡⟨ cong (λ c → unshift d c (shift 1 0 t2')) (+-comm 1 c) ⟩
            unshift d (c + 1) (shift 1 0 t2')
              ≡⟨ sym (unshiftShiftSwap z≤n s2') ⟩
            shift 1 0 (unshift d c t2') ∎
          ⟩
        unshift d (suc c) t1' [ 0 ≔ shift 1 0 (unshift d c t2') ] ∎
      ⟩
    unshift 1 0 (unshift d (suc c) t1' [ 0 ≔ shift 1 0 (unshift d c t2') ]) ∎
  r : tapp (tabs (unshift d (suc c) t1)) (unshift d c t2) →βP
      unshift d c (unshift 1 0 (t1' [ 0 ≔ shift 1 0 t2' ]))
  r rewrite eq = →βPbeta (unshiftLemma r1 s1) (unshiftLemma r2 s2)

substLemma : ∀ {n t1 t1' t2 t2'} →
             t1 →βP t1' → t2 →βP t2' → t1 [ n ≔ t2 ] →βP t1' [ n ≔ t2' ]
substLemma {n} {tvar n'} →βPvar r1 with n ≟ n'
...| yes p = r1
...| no p = →βPvar
substLemma (→βPapp r1 r2) r3 = →βPapp (substLemma r1 r3) (substLemma r2 r3)
substLemma (→βPabs r1) r2 = →βPabs $ substLemma r1 $ shiftLemma r2
substLemma {n} {t2 = t3} {t3'} (→βPbeta {t1} {t1'} {t2} {t2'} r1 r2) r3 = r where
  open ≡-Reasoning
  eq : unshift 1 0 (t1' [ 0 ≔ shift 1 0 t2' ]) [ n ≔ t3' ] ≡
       unshift 1 0 ((t1' [ suc n ≔ shift 1 0 t3' ]) [ 0 ≔ shift 1 0 (t2' [ n ≔ t3' ]) ])
  eq = begin
    unshift 1 0 (t1' [ 0 ≔ shift 1 0 t2' ]) [ n ≔ t3' ]
      ≡⟨ sym (unshiftSubstSwap' (t1' [ 0 ≔ shift 1 0 t2' ]) t3' (betaShifted' 0 t1' t2')) ⟩
    unshift 1 0 (t1' [ 0 ≔ shift 1 0 t2' ] [ suc n ≔ shift 1 0 t3' ])
      ≡⟨ cong (unshift 1 0) (substSubstSwap n 0 t1' t2' t3') ⟩
    unshift 1 0 ((t1' [ suc n ≔ shift 1 0 t3' ]) [ 0 ≔ shift 1 0 (t2' [ n ≔ t3' ]) ]) ∎
  r : tapp (tabs (t1 [ suc n ≔ shift 1 0 t3 ])) (t2 [ n ≔ t3 ]) →βP
      (unshift 1 0 (t1' [ 0 ≔ shift 1 0 t2' ])) [ n ≔ t3' ]
  r rewrite eq = →βPbeta (substLemma r1 (shiftLemma r3)) (substLemma r2 r3)

starLemma : ∀ {t t'} → t →βP t' → t' →βP t *
starLemma →βPvar = →βPvar
starLemma {tapp (tvar n) t2} (→βPapp p1 p2) =
  →βPapp (starLemma p1) (starLemma p2)
starLemma {tapp (tapp t1l t1r) t2} (→βPapp p1 p2) =
  →βPapp (starLemma p1) (starLemma p2)
starLemma {tapp (tabs t1) t2} {tapp (tvar _) t2'} (→βPapp () p2)
starLemma {tapp (tabs t1) t2} {tapp (tapp _ _) t2'} (→βPapp () p2)
starLemma {tapp (tabs t1) t2} {tapp (tabs t1') t2'} (→βPapp (→βPabs p1) p2) =
  →βPbeta (starLemma p1) (starLemma p2)
starLemma (→βPabs p1) = →βPabs (starLemma p1)
starLemma {tapp (tabs t1) t2} (→βPbeta {.t1} {t1'} {.t2} {t2'} p1 p2) =
  unshiftLemma
    (substLemma (starLemma p1) (shiftLemma (starLemma p2)))
    (betaShifted 0 t1' t2')

Diamond : ∀ {ℓ} {A : Set ℓ} (_R_ : Rel A ℓ) → Set ℓ
Diamond _R_ = ∀ {t1 t2 t3} → t1 R t2 → t1 R t3 → ∃ (λ t → t2 R t × t3 R t)

SemiConfluence : ∀ {ℓ} {A : Set ℓ} (_R_ : Rel A ℓ) → Set ℓ
SemiConfluence _R_ =
  ∀ {t1 t2 t3} → t1 R t2 → Star _R_ t1 t3 →
  ∃ (λ t → Star _R_ t2 t × Star _R_ t3 t)

Confluence : ∀ {ℓ} {A : Set ℓ} (_R_ : Rel A ℓ) → Set ℓ
Confluence _R_ = Diamond (Star _R_)

Diamond⇒SemiConfluence : ∀ {ℓ} {A : Set ℓ} {R : Rel A ℓ} → Diamond R → SemiConfluence R
Diamond⇒SemiConfluence diamond {t1} {t2} {.t1} r1 ε = t2 , ε , r1 ◅ ε
Diamond⇒SemiConfluence diamond {t1} {t2} {t3} r1 (r2 ◅ r3) =
  proj₁ d' , proj₁ (proj₂ d) ◅ proj₁ (proj₂ d') , proj₂ (proj₂ d') where
  d = diamond r1 r2
  d' = Diamond⇒SemiConfluence diamond (proj₂ (proj₂ d)) r3

SemiConfluence⇒Confluence :
  ∀ {ℓ} {A : Set ℓ} {R : Rel A ℓ} → SemiConfluence R → Confluence R
SemiConfluence⇒Confluence sconfluence {t1} {.t1} {t3} ε r2 = t3 , r2 , ε
SemiConfluence⇒Confluence sconfluence {t1} {t2} {t3} (r1 ◅ r2) r3 =
  proj₁ sc' , proj₁ (proj₂ sc') , proj₂ (proj₂ sc) ◅◅ proj₂ (proj₂ sc') where
  sc = sconfluence r1 r3
  sc' = SemiConfluence⇒Confluence sconfluence r2 (proj₁ (proj₂ sc))

diamond→βP : Diamond _→βP_
diamond→βP {t1} r1 r2 = (t1 *) , starLemma r1 , starLemma r2

confluence→βP : Confluence _→βP_
confluence→βP = SemiConfluence⇒Confluence $ Diamond⇒SemiConfluence diamond→βP

confluence→β : Confluence _→β_
confluence→β r1 r2 =
  proj₁ c ,
  Data.Star.concat (Data.Star.map →βP⊂→β* (proj₁ (proj₂ c))) ,
  Data.Star.concat (Data.Star.map →βP⊂→β* (proj₂ (proj₂ c))) where
  c = confluence→βP (Data.Star.map →β⊂→βP r1) (Data.Star.map →β⊂→βP r2)

