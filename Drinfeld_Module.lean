--import Mathlib.NumberTheory.FunctionField
import Mathlib.FieldTheory.Finite.GaloisField
import SkewPolynomials

variable (p : ℕ) [h_prime : Fact p.Prime] (n : ℕ)

scoped[DrinfeldModule] notation:max "𝔽_["p"]^"n => GaloisField p n


open DrinfeldModule Polynomial SkewPolynomial

variable (L : Type _) [Field L] [Algebra (𝔽_[p]^n)[X] L]

noncomputable def Frob : L →+* L where
  toFun     := fun x ↦ x^(p^n)
  map_one'  := by simp only [one_pow]
  map_mul'  := fun x y ↦ by
    simp; rw [mul_pow]
  map_zero' := by 
    simp only [ne_eq, gt_iff_lt, zero_pow_eq_zero]
    refine' pow_pos (Nat.Prime.pos h_prime.1) _
  map_add'  := fun x y ↦ by
    simp; 
    have hFieldAlg: Algebra (𝔽_[p]^n) L := by
      apply RingHom.toAlgebra ((algebraMap (𝔽_[p]^n)[X] L).comp
       (algebraMap (𝔽_[p]^n) (𝔽_[p]^n)[X]))
    have hChar: CharP L p := by
      apply charP_of_injective_algebraMap' (GaloisField p n) L p
    rw [add_pow_char_pow L x y]

namespace DrinfeldModule

instance : Algebra (𝔽_[p]^n) L[X; Frob p n L] := sorry

structure DrinfeldModule extends (𝔽_[p]^n)[X] →ₐ[(𝔽_[p]^n)] L[X; Frob p n L] where
  deriv : ∀ (a : (𝔽_[p]^n)[X]), (toFun a).coeff 0 = (algebraMap (𝔽_[p]^n)[X] L a)
  ne_trivial : ∃ (a : (𝔽_[p]^n)[X]), toFun a ≠ ((algebraMap (𝔽_[p]^n)[X] L) a)

end DrinfeldModule

