import Mathlib.Algebra.MonoidAlgebra.Basic

open AddMonoidAlgebra
noncomputable section

variable [Semiring k] [Add G] (φ : k →+* k) {f g : AddMonoidAlgebra k G}

namespace SkewMul

instance hasMul' (φ : k →+* k): Mul (AddMonoidAlgebra k G) :=
  ⟨fun f g => f.sum fun a₁ b₁ => g.sum fun a₂ b₂ => single (a₁ + a₂) (b₁ * (φ^[a₁] b₂))⟩


--set_option quotPrecheck false

scoped[SkewMul] notation:1000 f "**"φ g => (hasMul' φ) f g
