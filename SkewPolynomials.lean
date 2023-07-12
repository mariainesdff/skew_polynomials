import Mathlib.Algebra.MonoidAlgebra.Basic

noncomputable section

structure SkewPolynomial (R : Type _) (φ : R → R) [Semiring R] where ofFinsupp ::
  toFinsupp : AddMonoidAlgebra R ℕ
#align polynomial SkewPolynomial
#align polynomial.of_finsupp SkewPolynomial.ofFinsupp
#align polynomial.to_finsupp SkewPolynomial.toFinsupp

variable 

-- mathport name: polynomial
scoped[SkewPolynomial] notation:9000 R["X",φ] => SkewPolynomial R φ

open AddMonoidAlgebra
open Finsupp hiding single
open Function hiding Commute

open BigOperators SkewPolynomial

namespace SkewPolynomial

universe u

variable {R : Type u} {a b : R} {m n : ℕ}
