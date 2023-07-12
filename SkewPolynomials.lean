import Mathlib.Algebra.MonoidAlgebra.Basic

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

variable [Semiring R] (φ : R →+* R) {p q : R[X;φ]} 

theorem forall_iff_forall_finsupp (P : R[X;φ] → Prop) :
    (∀ p, P p) ↔ ∀ q : AddMonoidAlgebra R ℕ, P ⟨q⟩ :=
  ⟨fun h q => h ⟨q⟩, fun h ⟨p⟩ => h p⟩
#align polynomial.forall_iff_forall_finsupp SkewPolynomial.forall_iff_forall_finsupp

theorem exists_iff_exists_finsupp (P : R[X;φ] → Prop) :
    (∃ p, P p) ↔ ∃ q : AddMonoidAlgebra R ℕ, P ⟨q⟩ :=
  ⟨fun ⟨⟨p⟩, hp⟩ => ⟨p, hp⟩, fun ⟨q, hq⟩ => ⟨⟨q⟩, hq⟩⟩
#align polynomial.exists_iff_exists_finsupp SkewPolynomial.exists_iff_exists_finsupp

@[simp]
theorem eta (f : R[X;φ]) : SkewPolynomial.ofFinsupp f.toFinsupp = f := by cases f; rfl
#align polynomial.eta SkewPolynomial.eta

/-! ### Conversions to and from `AddMonoidAlgebra`

Since `R[X]` is not defeq to `AddMonoidAlgebra R ℕ`, but instead is a structure wrapping
it, we have to copy across all the arithmetic operators manually, along with the lemmas about how
they unfold around `Polynomial.ofFinsupp` and `Polynomial.toFinsupp`.
-/


section AddMonoidAlgebra

private irreducible_def add : R[X;φ] → R[X;φ] → R[X;φ]
  | ⟨a⟩, ⟨b⟩ => ⟨a + b⟩

private irreducible_def neg {T : Type _} [Ring T] (ψ : T →+* T) : T[X;ψ] → T[X;ψ]
  | ⟨a⟩ => ⟨-a⟩
