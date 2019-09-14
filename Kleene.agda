module Kleene {A : Set} where

open import Relation.Binary.PropositionalEquality using (setoid)
open import Relation.Binary.PropositionalEquality.Core as P using (_≡_)
open import Relation.Binary using (Reflexive ; Transitive ; Antisymmetric ; Poset ; _⇒_ ; Total ; Decidable ; DecSetoid ; Setoid)
open import Level
open import Data.Product using (_×_; _,_)
open import Data.Sum.Base
open import Data.Product
open import Function using (_∘_)

-- Kleene Algebra using Kozen axiomatization
-- https://www.cs.cornell.edu/~kozen/Papers/ka.pdf
-- "Unlike Salomaa's axiomatizations, the axiomatization given here is sound for all
-- interpretations over Kleene algebras."
-- Section 2 (Pg 5)
record Kleene : Set where
  constructor kleene
  field 0ₖ   : A
        1ₖ   : A
        _+_  : A → A → A
        _∙_  : A → A → A
        _*   : A → A

  -- The natural partial order on A
  -- a ≤ b ⇔ a + b = b
  _≤_ : A → A → Set
  _≤_ a b = (a + b) ≡ b

  infix  4  _≤_
  infixl 8  _+_
  infixl 9  _∙_
  infixl 10 _*
  field -- Kozen axioms
        [3]  : ∀ {a b c : A} → (a + (b + c)) ≡ ((a + b) + c)
        [4]  : ∀ {a b   : A} →        a + b ≡ (b + a)
        [5]  : ∀ {a     : A} →      (a + 0ₖ) ≡ a
        [6]  : ∀ {a     : A} →      (a + a)  ≡ a
        [7]  : ∀ {a b c : A} → (a ∙ (b ∙ c)) ≡ ((a ∙ b) ∙ c)
        [8]  : ∀ {a     : A} →      (a ∙ 1ₖ) ≡ a
        [9]  : ∀ {a     : A} →      (1ₖ ∙ a) ≡ a
        [10] : ∀ {a b c : A} → (a ∙ (b + c)) ≡ ((a ∙ b) + (a ∙ c))
        [11] : ∀ {a b c : A} → ((a + b) ∙ c) ≡ ((a ∙ c) + (b ∙ c))
        [12] : ∀ {a     : A} →      (0ₖ ∙ a) ≡ 0ₖ
        [13] : ∀ {a     : A} →      (a ∙ 0ₖ) ≡ 0ₖ
        [14] : ∀ {a     : A} → (1ₖ + (a ∙ (a *))) ≤ (a *)
        [15] : ∀ {a     : A} → (1ₖ + ((a *) ∙ a)) ≤ (a *)

        -- "Axioms (16-19) are studied by Pratt [24], who attributes (16) and (17) to
        -- Schröder and Dedekind. The equivalence of (16) and (18) (and, by symmetry,
        -- of (17) and (19)) are proved in [24]."
        -- [24] Vaughan Pratt Dynamic algebras as a well-behaved fragment of relation
        -- algebras In D Pigozzi, editor, Proc Conf on Algebra and Computer Science,
        -- Lect Notes in Comput Sci Springer-Verlag, June 1998
        --
        -- A Completeness Theorem for Kleene Algebras and the Algebra of Regular Events
        -- Dexter Kozen
        [16] : ∀ {a b x : A} → ((b + (a ∙ x)) ≤ x) → (((a *) ∙ b) ≤ x)
        [17] : ∀ {a b x : A} → ((b + (x ∙ a)) ≤ x) → (((a *) ∙ b) ≤ x)
        [18] : ∀ {a   x : A} → (     (a ∙ x)  ≤ x) → (((a *) ∙ x) ≤ x)
        [19] : ∀ {a   x : A} → (     (x ∙ a)  ≤ x) → ((x ∙ (a *)) ≤ x)

  open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong; cong-app; subst; cong₂)
  setoidₖ : Setoid zero zero
  setoidₖ = setoid A
  open import Relation.Binary.Reasoning.Setoid setoidₖ
  open import Algebra                        using (IdempotentCommutativeMonoid; Monoid)
  open import Algebra.FunctionProperties _≡_ using (Idempotent ; _IdempotentOn_ ; IdempotentFun ; Commutative ; LeftIdentity ; RightIdentity ; Congruent₁
                                                   ; Congruent₂ ; Associative ; _DistributesOverˡ_ ; _DistributesOverʳ_ ; _DistributesOver_ ; LeftCongruent ; RightCongruent)
  open import Algebra.Structures         _≡_ using (IsMagma)

  +-cong : Congruent₂ _+_
  +-cong = cong₂ _+_

  +-congˡ : LeftCongruent _+_
  +-congˡ {a} i≡j = +-cong refl i≡j

  +-congʳ : RightCongruent _+_
  +-congʳ {a} i≡j = +-cong i≡j refl

  ∙-cong : Congruent₂ _∙_
  ∙-cong = cong₂ _∙_

  ∙-congˡ : LeftCongruent _∙_
  ∙-congˡ {a} i≡j = ∙-cong refl i≡j

  ∙-congʳ : RightCongruent _∙_
  ∙-congʳ {a} i≡j = ∙-cong i≡j refl

  -- ∀ {a b : A} → a ≡ b → (a *) ≡ (b *)
  *-cong : Congruent₁ _*
  *-cong = cong _*

  +-assoc : Associative _+_
  +-assoc a b c = sym ([3] {a = a} {b = b} {c = c})

  ∙-assoc : Associative _∙_
  ∙-assoc a b c = sym ([7] {a = a} {b = b} {c = c})

  isMagma : IsMagma _+_
  isMagma = record { isEquivalence = P.isEquivalence
                   ; ∙-cong        = +-cong
                   }

  +-comm : Commutative _+_
  +-comm a b = [4] {a = a} {b = b}

  +-identityˡ : LeftIdentity 0ₖ _+_
  +-identityˡ a = begin             0ₖ + a
                  ≡⟨ +-comm 0ₖ a ⟩  a  + 0ₖ
                  ≡⟨ [5] {a = a} ⟩  a       ∎

  +-identityʳ : RightIdentity 0ₖ _+_
  +-identityʳ a = [5] {a = a}

  +-idempotentOn : ∀ {a : A} → _+_ IdempotentOn a
  +-idempotentOn = [6]

  +-idem : Idempotent _+_
  +-idem a = +-idempotentOn {a = a}

  ∙-identityʳ : RightIdentity 1ₖ _∙_
  ∙-identityʳ a = [8] {a}

  ∙-identityˡ : LeftIdentity 1ₖ _∙_
  ∙-identityˡ a = [9] {a}

  +-0-idempotentCommutativeMonoid : IdempotentCommutativeMonoid _ _
  +-0-idempotentCommutativeMonoid = record { Carrier = A
                                           ; _≈_     = _≡_
                                           ; _∙_     = _+_
                                           ; ε       = 0ₖ
                                           ; isIdempotentCommutativeMonoid = record { isCommutativeMonoid = record { isSemigroup = record { isMagma = isMagma
                                                                                                                                          ; assoc   = +-assoc
                                                                                                                                          }
                                                                                                                   ; identityˡ = +-identityˡ
                                                                                                                   ; comm      = +-comm
                                                                                                                   }
                                                                                    ; idem = +-idem
                                                                                    }
                                           }

  ∙-1-monoid : Monoid _ _
  ∙-1-monoid = record { Carrier  = A
                      ; _≈_      = _≡_
                      ; _∙_      = _∙_
                      ; ε        = 1ₖ
                      ; isMonoid = record { isSemigroup = record { isMagma = record { isEquivalence = P.isEquivalence
                                                                                    ; ∙-cong        = ∙-cong
                                                                                    }
                                                                 ; assoc = ∙-assoc
                                                                 }
                                          ; identity = (∙-identityˡ , ∙-identityʳ)
                                          }
                      }

  -- ∀ x y z → (x * (y + z)) ≈ ((x * y) + (x * z))
  ∙-distribˡ-+ : _∙_ DistributesOverˡ _+_
  ∙-distribˡ-+ a b c = [10] {a = a} {b = b} {c = c}

  -- ∀ x y z → ((y + z) * x) ≈ ((y * x) + (z * x))
  ∙-distribʳ-+ : _∙_ DistributesOverʳ _+_
  ∙-distribʳ-+ a b c = [11] {a = b} {b = c} {c = a}

  -- (* DistributesOverˡ +) × (* DistributesOverʳ +)
  ∙-distrib-+ : _∙_ DistributesOver _+_
  ∙-distrib-+ = ∙-distribˡ-+ , ∙-distribʳ-+

  ≤-refl : Reflexive {A = A} _≤_
  ≤-refl {a} = +-idem a

  ≡⇒≤ : _≡_ ⇒ _≤_
  ≡⇒≤ refl = ≤-refl

  implied : ∀ {a b : A} → a ≡ b → a ≤ b
  implied {a} {b} a≡b = a≤b
          where a≤b : a ≤ b
                a≤b = ≡⇒≤ a≡b

  -- TODO better name for this
  otherway : ∀ {a b : A} → a ≤ b → (a + b) ≡ b
  otherway {a} {b} a≤b = a+b≡b
          where a+b≡b : (a + b) ≡ b
                a+b≡b = a≤b

  ≤-trans : Transitive {A = A} _≤_
  ≤-trans {a} {b} {c} a≤b b≤c = a≤c
    where a≤c : a ≤ c
          a≤c = begin                     a       + c
                ≡⟨ +-congˡ (sym b≤c)   ⟩  a + (b  + c)
                ≡⟨ sym (+-assoc a b c) ⟩ (a +  b) + c
                ≡⟨ +-congʳ      a≤b    ⟩      (b  + c)
                ≡⟨ b≤c                 ⟩            c ∎

  ≤-antisym : Antisymmetric _≡_ _≤_
  ≤-antisym {a} {b} a≤b b≤a = a≡b
          where a≡b : a ≡ b
                a≡b = begin                    a
                      ≡⟨ sym b≤a        ⟩ (b + a)
                      ≡⟨ +-comm b a     ⟩ (a + b)
                      ≡⟨ a≤b            ⟩      b  ∎

  0≤a : ∀ {a : A} → 0ₖ ≤ a
  0≤a {a} = +-identityˡ a

  0≤a* : ∀ {a : A} → 0ₖ ≤ a *
  0≤a* {a} = 0≤a {a = a *} -- +-identityˡ (x *)

  partialOrder : Poset _ _ _
  partialOrder = record { Carrier = A
                        ; _≈_     = _≡_
                        ; _≤_     = _≤_
                        ; isPartialOrder = record { isPreorder = record { isEquivalence = P.isEquivalence
                                                                        ; reflexive     = implied
                                                                        ; trans         = ≤-trans
                                                                        }
                                                  ; antisym    = ≤-antisym
                                                  }
                        }
  open import Relation.Binary.Lattice using (Minimum ; Supremum ; BoundedJoinSemilattice)

  -- `x + y` is an upper bound for `x`
  x≤x+y : ∀ {x y : A} → x ≤ (x + y)
  x≤x+y {x} {y} = begin                      (x + (x  + y))
                  ≡⟨ sym (+-assoc x x y) ⟩  ((x +  x) + y)
                  ≡⟨ +-congʳ (+-idem x)  ⟩        (x  + y) ∎

  -- `x + y` is an upper bound for `y`
  y≤x+y : ∀ {x y : A} → y ≤ (x + y)
  y≤x+y {x} {y} = begin                      y + (x  + y)
                  ≡⟨ +-congˡ (+-comm x y) ⟩  y + (y  + x)
                  ≡⟨ sym (+-assoc y y x)  ⟩ (y +  y) + x
                  ≡⟨ +-congʳ (+-idem y)   ⟩      (y  + x)
                  ≡⟨ +-comm  y x          ⟩      (x  + y) ∎

  -- `x + y` is the /least/ upper bound
  lub : ∀ {x y : A} → (z : A) → x ≤ z → y ≤ z → (x + y) ≤ z
  lub {x} {y} z x≤z y≤z = x+y≤z
    where x+y≤z : (x + y) ≤ z
          x+y≤z = begin              (x +  y) + z
                  ≡⟨ +-assoc x y z ⟩  x + (y  + z)
                  ≡⟨ +-congˡ y≤z   ⟩  x       + z
                  ≡⟨ x≤z           ⟩            z ∎

  -- least upper bound
  sup : Supremum {A = A} _≤_ _+_
  sup x y = x≤x+y , y≤x+y , lub

  min : Minimum _≤_ 0ₖ
  min = +-identityˡ -- TODO 0≤a

  boundedJoinSemilattice : BoundedJoinSemilattice _ _ _
  boundedJoinSemilattice = record { Carrier = A
                                  ; _≈_     = _≡_
                                  ; _≤_     = _≤_
                                  ; _∨_     = _+_
                                  ; ⊥       = 0ₖ
                                  ; isBoundedJoinSemilattice = record { isJoinSemilattice = record { isPartialOrder = Poset.isPartialOrder partialOrder
                                                                                                   ; supremum       = sup
                                                                                                   }
                                                                      ; minimum = min
                                                                      }
                                  }

  -- helper function
  reassociate : ∀ {a b c d : A} → ((a + b) + (c + d)) ≡ (a + (b + c) + d)
  reassociate {a} {b} {c} {d} = begin                            (a +   b + (c  + d))
                              ≡⟨ +-assoc a b (c + d)           ⟩  a +  (b + (c  + d))
                              ≡⟨ +-congˡ (sym (+-assoc b c d)) ⟩  a + ((b +  c) + d)
                              ≡⟨ sym (+-assoc a (b + c) d)     ⟩ (a +  (b +  c) + d) ∎

  -- another helper
  -- y + x + (y + x) ≡ x + (y + (y + x))
  reassociate' : ∀ {a b c d : A} → (a + b) + (c + d) ≡ a + (b + (c + d))
  reassociate' {a} {b} {c} {d} = +-assoc a b (c + d)

  ≡-substₗ : ∀ {x y z : A} → x ≡ z → x ≡ y → z ≡ y
  ≡-substₗ {_} {y} = subst (λ t → t ≡ y)

  ≡-substᵣ : ∀ {x y z : A} → y ≡ z → x ≡ y → x ≡ z
  ≡-substᵣ {x} {_} = subst (λ t → x ≡ t)

  ≤-substₗ : ∀ {x y z : A} → x ≡ z → x ≤ y → z ≤ y
  ≤-substₗ {_} {y} = subst (λ t → t ≤ y)

  ≤-substᵣ : ∀ {x y z : A} → y ≡ z → x ≤ y → x ≤ z
  ≤-substᵣ {x} {_} = subst (λ t → x ≤ t)

  -- "the relation ≤ ... is monotone with repsect to all the Kleene algebra operators in the sense that
  -- if a ≤ b, then ac ≤ bc, ca ≤ cb, a + c ≤ b + c, and a* ≤ b*"
  +-monoˡ-≤ : ∀ c → (_+ c) Relation.Binary.Preserves _≤_ ⟶ _≤_
  +-monoˡ-≤ c {a} {b} a≤b = begin                                  (a +  c) + (b  + c)
                            ≡⟨ +-congˡ (+-comm b c)              ⟩ (a +  c) + (c  + b)
                            ≡⟨ reassociate                       ⟩  a + (c  +  c) + b
                            ≡⟨ cong (λ x → a + x + b) (+-idem c) ⟩ (a +  c)       + b
                            ≡⟨ +-assoc a c b                     ⟩  a + (c        + b)
                            ≡⟨ +-congˡ (+-comm c b)              ⟩  a + (b  +  c)
                            ≡⟨ sym (+-assoc a b c)               ⟩ (a +  b) +  c
                            ≡⟨ +-cong a≤b refl                   ⟩       b  +  c       ∎

  +-monoʳ-≤ : ∀ c → (c +_) Relation.Binary.Preserves _≤_ ⟶ _≤_
  +-monoʳ-≤ c {a} {b} a≤b = begin                     (c + a) + (c + b)
                            ≡⟨ +-congˡ (+-comm c b) ⟩ (c + a) + (b + c)
                            ≡⟨ +-congʳ (+-comm c a) ⟩ (a + c) + (b + c)
                            ≡⟨ +-monoˡ-≤ c a≤b      ⟩           (b + c)
                            ≡⟨ +-comm b c           ⟩           (c + b) ∎


  +-mono-≤ : _+_ Relation.Binary.Preserves₂ _≤_ ⟶ _≤_ ⟶ _≤_
  +-mono-≤ {a} {b} {c} {d} a≤b c≤d = begin                               ((a +  c) + (b  + d))
                                     ≡⟨ +-congˡ (+-comm b d)           ⟩ ((a +  c) + (d  + b))
                                     ≡⟨ reassociate                    ⟩  (a + (c  +  d) + b)
                                     ≡⟨ cong (λ c+d → a + c+d + b) c≤d ⟩  (a +  d) +  b
                                     ≡⟨ +-congʳ (+-comm a d)           ⟩  (d +  a) +  b
                                     ≡⟨ +-assoc d a b                  ⟩   d + (a  +  b)
                                     ≡⟨ +-congˡ a≤b                    ⟩   d +        b
                                     ≡⟨ +-comm d b                     ⟩  (b +        d)       ∎

  ∙-monoˡ-≤ : ∀ c → (_∙ c) Relation.Binary.Preserves _≤_ ⟶ _≤_
  ∙-monoˡ-≤ c {a} {b} a≤b = begin                         ((a ∙ c) + (b  ∙ c))
                            ≡⟨ sym (∙-distribʳ-+ c a b) ⟩  (a      +  b) ∙ c
                            ≡⟨ ∙-congʳ a≤b              ⟩            (b  ∙ c) ∎

  ∙-monoʳ-≤ : ∀ c → (c ∙_) Relation.Binary.Preserves _≤_ ⟶ _≤_
  ∙-monoʳ-≤ c {a} {b} a≤b = begin            ((c ∙  a) + (c ∙ b))
                            ≡⟨ sym [10]    ⟩   c ∙ (a       + b)
                            ≡⟨ ∙-congˡ a≤b ⟩  (c ∙            b) ∎

  +-mono-≡ : _+_ Relation.Binary.Preserves₂ _≡_ ⟶ _≡_ ⟶ _≡_
  +-mono-≡ {a} {b} {c} {d} a≡b c≡d = ≡-substᵣ (+-congʳ a≡b) (≡-substₗ (+-congˡ (sym c≡d)) refl)

  ∙-mono-≡ : _∙_ Relation.Binary.Preserves₂ _≡_ ⟶ _≡_ ⟶ _≡_
  ∙-mono-≡ {a} {b} {c} {d} a≡b c≡d = ≡-substᵣ (∙-congʳ a≡b) (≡-substₗ (∙-congˡ (sym c≡d)) refl)

  helper : ∀ {a b x : A} → (a ∙ x) ≤ (x ∙ b) → ((x + a ∙ x ∙ (b *)) ≤ (x + (x ∙ b ∙ (b *))))
  helper {a} {b} {x} ax≤xb = (+-monoʳ-≤ x) (∙-monoˡ-≤ (b *) ax≤xb)

  1+aa*b≤a*b : ∀ {a b : A} → (1ₖ + (a ∙ (a *))) ∙ b ≤ (a *) ∙ b
  1+aa*b≤a*b {a} {b} = ∙-monoˡ-≤ b [14]

  1+aa*b≡b+aa*b : ∀ {a b : A} → ((1ₖ + (a ∙ (a *))) ∙ b) ≡ (b + (a ∙ ((a *) ∙ b)))
  1+aa*b≡b+aa*b {a} {b} = begin                                ((1ₖ      +  (a ∙  (a *))) ∙ b)
                          ≡⟨ ∙-distribʳ-+ b 1ₖ ((a ∙ (a *))) ⟩  (1ₖ ∙ b) + ((a ∙  (a *))  ∙ b)
                          ≡⟨ +-congʳ (∙-identityˡ b)         ⟩        b  +  (a ∙  (a *)   ∙ b)
                          ≡⟨ +-congˡ (∙-assoc a ((a *)) b)   ⟩       (b  +  (a ∙ ((a *)   ∙ b))) ∎

  b+aa*b≤a*b : ∀ {a b : A} → (b + (a ∙ ((a *) ∙ b))) ≤ (a *) ∙ b
  b+aa*b≤a*b {a} {b} = subst (λ t → t ≤ a * ∙ b) 1+aa*b≡b+aa*b 1+aa*b≤a*b

  -- strengthen axiom [14] from an inequality into an equality
  1+aa*≡a* : ∀ {a : A} → 1ₖ + a ∙ a * ≡ a *
  1+aa*≡a* {a} = ≤-antisym 1+aa*≤a* a*≤1+aa*
       where
             1+aa*≤a* : 1ₖ + a ∙ a * + a * ≡ a *
             1+aa*≤a* = [14] {a = a}
             [16]' : 1ₖ + a ∙ (1ₖ + a ∙ a *) ≤ 1ₖ + a ∙ a *
                   → a * ∙ 1ₖ                ≤ 1ₖ + a ∙ a *
             [16]'  = [16] {a = a} {b = 1ₖ} {x = 1ₖ + a ∙ a *}
             a*≤1+aa* : a * ≤ 1ₖ + a ∙ a *
             a*≤1+aa* = ≤-substₗ (∙-identityʳ (a *)) ([16]' (+-monoʳ-≤ 1ₖ (∙-monoʳ-≤ a [14])))

  -- strengthen axiom [15] from an inequality into an equality
  1+a*a≡a* : ∀ {a : A} → 1ₖ + a * ∙ a ≡ a *
  1+a*a≡a* {a} = ≤-antisym 1+a*a≤a* a*≤1+a*a
       where
             1+a*a≤a* : 1ₖ + a * ∙ a ≤ a *
             1+a*a≤a* = [15] {a = a}
             [17]' : 1ₖ + (1ₖ + a * ∙ a) ∙ a ≤ 1ₖ + a * ∙ a
                   → a * ∙ 1ₖ                ≤ 1ₖ + a * ∙ a
             [17]' = [17] {a = a} {b = 1ₖ} {x = 1ₖ + a * ∙ a}
             a*≤1+a*a : a * ≤ 1ₖ + a * ∙ a
             a*≤1+a*a = ≤-substₗ (∙-identityʳ (a *)) ([17]' (+-monoʳ-≤ 1ₖ (∙-monoˡ-≤ a [15])))

  a+b≤c→[a≤c]×[b≤c] : ∀ {a b c : A} → a + b ≤ c → a ≤ c × b ≤ c
  a+b≤c→[a≤c]×[b≤c] {a} {b} {c} a+b≤c = a≤c , b≤c
     where
        -- proof sketch:
        --     0 ≤     b
        -- a + 0 ≤ a + b
        -- a     ≤ a + b
        0≤b : 0ₖ ≤ b
        0≤b = 0≤a {a = b}
        a+0≤a+b : a + 0ₖ ≤ a + b
        a+0≤a+b = +-monoʳ-≤ a 0≤b
        a≤a+b : a ≤ a + b
        a≤a+b = ≤-substₗ (+-identityʳ a) a+0≤a+b
        -- a≤a+b = ≤-substₗ (+-identityʳ a) (+-monoʳ-≤ a (0≤a {x = b}))
        -- or lol
        a≤a+b' : a ≤ a + b
        a≤a+b' = begin                      a + (a  + b)
                 ≡⟨  sym (+-assoc a a b) ⟩ (a +  a) + b
                 ≡⟨  +-congʳ (+-idem a)  ⟩      (a  + b) ∎
        a≤c : a ≤ c
        a≤c = ≤-trans a≤a+b a+b≤c
        b≤a+b : b ≤ a + b
        b≤a+b = begin                       b + (a  + b)
                ≡⟨  +-congˡ (+-comm a b) ⟩  b + (b  + a)
                ≡⟨  sym (+-assoc b b a)  ⟩ (b +  b) + a
                ≡⟨  +-congʳ (+-idem b)   ⟩  b       + a
                ≡⟨  +-comm b a           ⟩  a       + b ∎
        b≤c : b ≤ c
        b≤c = ≤-trans b≤a+b a+b≤c

  [a≤c]×[b≤c]→a+b≤c : ∀ {a b c : A} → a ≤ c × b ≤ c → a + b ≤ c
  [a≤c]×[b≤c]→a+b≤c {a} {b} {c} (a≤c , b≤c) = lub c a≤c b≤c

  1≤a* : ∀ {a : A} → 1ₖ ≤ a *
  1≤a*   {a} = proj₁ (a+b≤c→[a≤c]×[b≤c] ([14] {a = a}))
  -- 1≤a*' : ∀ {a : A} → 1ₖ ≤ a *
  -- 1≤a*'   {a} = proj₁ (a+b≤c→[a≤c]×[b≤c] ([15] {a = a}))
  1≤a*' : ∀ {a : A} → 1ₖ ≤ a *
  1≤a*' {a} = begin                              (1ₖ +            a *)
              ≡⟨ +-congˡ (sym 1+aa*≡a*)        ⟩  1ₖ + (1ₖ  + a ∙ a *)
              ≡⟨ sym (+-assoc 1ₖ 1ₖ (a ∙ a *)) ⟩ (1ₖ +  1ₖ) + a ∙ a *
              ≡⟨ +-congʳ (+-idem 1ₖ)           ⟩        1ₖ  + a ∙ a *
              ≡⟨ 1+aa*≡a*                      ⟩                  a * ∎

  aa*≤a* : ∀ {a : A} → a ∙ a * ≤ a *
  aa*≤a* {a} = proj₂ (a+b≤c→[a≤c]×[b≤c] ([14] {a = a}))

  a*a≤a* : ∀ {a : A} → a * ∙ a ≤ a *
  a*a≤a* {a} = proj₂ (a+b≤c→[a≤c]×[b≤c] ([15] {a = a}))

  a1≤aa* : ∀ {a : A} → a ∙ 1ₖ ≤ a ∙ a *
  a1≤aa* {a} = ∙-monoʳ-≤ a 1≤a*

  a≤aa* : ∀ {a : A} → a ≤ a ∙ a *
  a≤aa* {a} = ≤-substₗ (∙-identityʳ a) a1≤aa*

  a≤1+aa* : ∀ {a : A} → a ≤ 1ₖ + a ∙ a *
  a≤1+aa* {a} = begin  a + (1ₖ + a ∙ a *)
                ≡⟨ sym (+-assoc  a  1ₖ (a ∙ a *) ) ⟩ (a  +  1ₖ) + a ∙ a *
                ≡⟨ +-congʳ (+-comm a 1ₖ)           ⟩ (1ₖ +  a)  + a ∙ a *
                ≡⟨      +-assoc  1ₖ a  (a ∙ a *)   ⟩  1ₖ + (a   + a ∙ a *)
                ≡⟨ +-congˡ a≤aa*                   ⟩  1ₖ        + a ∙ a * ∎

  -- a + a* ≡ a*
  a≤a* : ∀ {a : A} → a ≤ a *
  a≤a* = ≤-substᵣ 1+aa*≡a* a≤1+aa*

  1+a≤a* : ∀ {a : A} → 1ₖ + a ≤ a *
  1+a≤a* {a} = lub (a *) 1≤a* a≤a*

  0+a≤a* : ∀ {a : A} → 0ₖ + a ≤ a *
  0+a≤a* {a} = lub (a *) 0≤a* a≤a*

  a*+aa*≤a* : ∀ {a : A} → a * + a ∙ a * ≤ a *
  a*+aa*≤a* {a} = lub (a *) ≤-refl aa*≤a*

  a*a*≤a* : ∀ {a : A} → a * ∙ a * ≤ a *
  a*a*≤a* = [16] a*+aa*≤a*

  -- 1ₖ + a*a* ≤ a*
  1+a*a*≤a* : ∀ {a : A} → 1ₖ + a * ∙ a * ≤ a *
  1+a*a*≤a* {a} = lub (a *) 1≤a* a*a*≤a*

  1+a[1+aa*]≤1+aa* : ∀ {a : A} → 1ₖ + a ∙ (1ₖ + a ∙ a *) ≤ 1ₖ + a ∙ a *
  1+a[1+aa*]≤1+aa* {a} = +-monoʳ-≤ 1ₖ (∙-monoʳ-≤ a [14])

  a**≤a* : ∀ {a : A} → (a *) * ≤ a *
  a**≤a* {a} = ≤-substₗ (∙-identityʳ (a * *)) ([16] {b = 1ₖ} (1+a*a*≤a* {a = a}))

  a*≤a** : ∀ {a : A} → a * ≤ (a *) *
  a*≤a** {a} = a≤a* {a = a *}

  -- a**≡a* : ∀ {a : A} → (a *) * ≡ a *
  *-idem : IdempotentFun _*
  *-idem a = ≤-antisym (a**≤a* {a = a}) (a*≤a** {a = a})

  a*≤a*a* : ∀ {a : A} → a * ≤ a * ∙ a *
  a*≤a*a* {a} = ≤-substᵣ (∙-congˡ (*-idem a)) a*≤a*a**
    where
      a*≤a*a** : a * ≤ a * ∙ a * *
      a*≤a*a** = a≤aa* {a = a *}

  a*a*≡a* : ∀ {a : A} → a * ∙ a * ≡ a *
  a*a*≡a* = ≤-antisym a*a*≤a* a*≤a*a*

  1+1≤1* : 1ₖ + 1ₖ ≤ 1ₖ *
  1+1≤1* = 1+a≤a* {a = 1ₖ}

  1+1*≤1** : 1ₖ + (1ₖ *) ≤ (1ₖ *) *
  1+1*≤1** = 1+a≤a* {a = 1ₖ *}

  1+1*≤1* : 1ₖ + (1ₖ *) ≤ (1ₖ *)
  1+1*≤1* = ≤-substᵣ (*-idem 1ₖ) 1+1*≤1**

  1+11≤1 : 1ₖ + 1ₖ ∙ 1ₖ ≤ 1ₖ
  1+11≤1 = ≤-substₗ 11≡1+11 11≤1
     where
       1≤1 : 1ₖ ≤ 1ₖ
       1≤1 = ≤-refl
       11≤1 : 1ₖ ∙ 1ₖ ≤ 1ₖ
       11≤1 = ≤-substₗ (sym (∙-identityˡ 1ₖ)) 1≤1
       -- TODO can probably clean this proof up
       -- TODO use `1+1≡1` instead of `+-idem 1ₖ`
       11≡1+11 : 1ₖ ∙ 1ₖ ≡ 1ₖ + 1ₖ ∙ 1ₖ
       11≡1+11 = subst (λ t → t ≡ 1ₖ + t) (sym (∙-identityʳ 1ₖ))  (sym (+-idem 1ₖ)) --

  1*1≤1 : 1ₖ * ∙ 1ₖ ≤ 1ₖ
  1*1≤1 = [16] 1+11≤1

  1*≡1*1 : 1ₖ * ≡ 1ₖ * ∙ 1ₖ
  1*≡1*1 = sym (∙-identityʳ (1ₖ *))

  -- 1≤11*
  1*≤1 : 1ₖ * ≤ 1ₖ
  1*≤1 = ≤-trans (≡⇒≤ 1*≡1*1) 1*1≤1

  1≤1* : 1ₖ ≤ 1ₖ *
  1≤1* = 1≤a* {a = 1ₖ}

  1*≡1 : 1ₖ * ≡ 1ₖ
  1*≡1 = ≤-antisym 1*≤1 1≤1*

  0*≡1 : 0ₖ * ≡ 1ₖ
  0*≡1 = begin                                        0ₖ *
         ≡⟨ sym (1+aa*≡a* {a = 0ₖ})     ⟩ 1ₖ +  0ₖ ∙  0ₖ *
         ≡⟨⟩                              1ₖ + (0ₖ ∙ (0ₖ *))
         ≡⟨ +-congˡ ([12] {a = 0ₖ *})   ⟩ 1ₖ + (0ₖ)
         ≡⟨ +-identityʳ 1ₖ              ⟩ 1ₖ                 ∎

  0≤0 : 0ₖ ≤ 0ₖ
  0≤0 = ≤-refl

  0≤1 : 0ₖ ≤ 1ₖ
  0≤1 = +-identityˡ 1ₖ

  1≤1 : 1ₖ ≤ 1ₖ
  1≤1 = ≤-refl

  0+0≡0 : 0ₖ + 0ₖ ≡ 0ₖ
  0+0≡0 = +-idem 0ₖ

  1+0≡1 : 1ₖ + 0ₖ ≡ 1ₖ
  1+0≡1 = +-identityʳ 1ₖ

  0+1≡1 : 0ₖ + 1ₖ ≡ 1ₖ
  0+1≡1 = +-identityˡ 1ₖ

  1+1≡1 : 1ₖ + 1ₖ ≡ 1ₖ
  1+1≡1 = +-idem 1ₖ

  a+aa*≤a* : ∀ {a : A} → a + a ∙ a * ≤ a *
  a+aa*≤a* {a} = lub (a *) a≤a* (aa*≤a* {a = a})

  *-mono-≤ : ∀ {a b : A} → a ≤ b → (a *) ≤ (b *)
  *-mono-≤ {a} {b} a≤b = ≤-trans a*≤a*1 ([16] {a = a} 1+ab*≤b*)
    where
      a*≤a*1 : a * ≤ a * ∙ 1ₖ
      a*≤a*1 = ≡⇒≤ (sym (∙-identityʳ (a *)))
      -- proof sketch for 1 + ab* ≤ 1 + bb*
      --      a         ≤      b          given
      --      a ∙ (b*)  ≤      b ∙ (b*)   by monotonicity of (∙ (b*))
      -- 1 + (a ∙ (b*)) ≤ 1 + (b ∙ (b*))  by monotonicity of (1 +)
      1+ab*≤1+bb* : 1ₖ + a ∙ b * ≤ 1ₖ + b ∙ b *
      1+ab*≤1+bb* = +-monoʳ-≤ 1ₖ (∙-monoˡ-≤ (b *) a≤b)
      1+ab*≤b* : 1ₖ + a ∙ b * ≤ b *
      1+ab*≤b* = ≤-trans 1+ab*≤1+bb* ([14] {a = b})
