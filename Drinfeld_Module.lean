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
  map_mul'  := sorry
  map_zero' := sorry
  map_add'  := sorry
namespace DrinfeldModule


structure DrinfeldModule where
  toFun : (𝔽_[p]^n)[X] → L[X; Frob p n L] 

end DrinfeldModule


--def Frob : 

