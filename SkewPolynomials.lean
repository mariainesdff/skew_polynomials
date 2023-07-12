import Mathlib.Algebra.MonoidAlgebra.Basic

open AddMonoidAlgebra
noncomputable section

structure SkewPolynomial (R : Type _) [Semiring R] (φ : R →+* R) where ofFinsupp ::
  toFinsupp : AddMonoidAlgebra R ℕ


scoped[SkewPolynomial] notation:max R"[X;"φ"]" => SkewPolynomial R φ

open AddMonoidAlgebra
open Finsupp hiding single
open Function hiding Commute

open BigOperators SkewPolynomial

namespace SkewPolynomial

universe u

variable {R : Type u} {a b : R} {m n : ℕ}

section Semiring

variable [Semiring R] {φ : R →+* R} {p q : R[X;φ]} 

theorem forall_iff_forall_finsupp (P : R[X;φ] → Prop) :
    (∀ p, P p) ↔ ∀ q : AddMonoidAlgebra R ℕ, P ⟨q⟩ :=
  ⟨fun h q => h ⟨q⟩, fun h ⟨p⟩ => h p⟩

theorem exists_iff_exists_finsupp (P : R[X;φ] → Prop) :
    (∃ p, P p) ↔ ∃ q : AddMonoidAlgebra R ℕ, P ⟨q⟩ :=
  ⟨fun ⟨⟨p⟩, hp⟩ => ⟨p, hp⟩, fun ⟨q, hq⟩ => ⟨⟨q⟩, hq⟩⟩

@[simp]
theorem eta (f : R[X;φ]) : SkewPolynomial.ofFinsupp f.toFinsupp = f := by cases f; rfl

/-! ### Conversions to and from `AddMonoidAlgebra`

Since `R[X;φ]` is not defeq to `AddMonoidAlgebra R ℕ`, but instead is a structure wrapping
it, we have to copy across all the arithmetic operators manually, along with the lemmas about how
they unfold around `Polynomial.ofFinsupp` and `Polynomial.toFinsupp`.
-/


section AddMonoidAlgebra

private irreducible_def add : R[X;φ] → R[X;φ] → R[X;φ]
  | ⟨a⟩, ⟨b⟩ => ⟨a + b⟩

private irreducible_def neg {S : Type _} [Ring S] {ψ : S →+* S} : S[X;ψ] → S[X;ψ]
  | ⟨a⟩ => ⟨-a⟩

private def AddMonoidAlgebra.mul' (φ : R →+* R) (f g : AddMonoidAlgebra R ℕ): (AddMonoidAlgebra R ℕ) :=
  f.sum fun a₁ b₁ => g.sum fun a₂ b₂ => single (a₁ + a₂) (b₁ * (φ^[a₁] b₂))

private irreducible_def mul : R[X;φ] → R[X;φ] → R[X;φ]
  | ⟨a⟩, ⟨b⟩ => ⟨AddMonoidAlgebra.mul' φ a b⟩

instance zero : Zero R[X;φ] :=
  ⟨⟨0⟩⟩

instance one : One R[X;φ] :=
  ⟨⟨1⟩⟩

instance add' : Add R[X;φ] :=
  ⟨add⟩

instance neg' {S : Type u} [Ring S] {φ : S →+* S} : Neg S[X;φ] :=
  ⟨neg⟩

instance sub {S : Type u} [Ring S] {φ : S →+* S}: Sub S[X;φ] :=
  ⟨fun a b => a + -b⟩

instance mul' : Mul R[X;φ] :=
  ⟨mul⟩

instance AddCommMonoid : AddCommMonoid R[X;φ] :=
  inferInstanceAs (AddCommMonoid (AddMonoidAlgebra R ℕ))
  

instance Semiring : Semiring R[X;φ] :=
  {Finsupp.addCommMonoid with
    zero := 0
    one := 1
    mul := (· * ·)
    add := (· + ·) 
  
    left_distrib := sorry
    right_distrib := sorry
    zero_mul := by
      intros f
      simp only [zero_mul]
    mul_zero := by
      intros f
      simp
    mul_assoc := sorry
    one_mul := sorry
    mul_one := sorry
    natCast_zero := sorry
    natCast_succ := sorry
    npow := sorry
    npow_zero := sorry
    npow_succ := sorry }

  


namespace SkewMul




--set_option quotPrecheck false

--scoped[SkewMul] notation:1000 f "**"φ g => (hasMul' φ) f g
