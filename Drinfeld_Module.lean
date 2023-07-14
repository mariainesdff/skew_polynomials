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

instance : Algebra (𝔽_[p]^n) L[X; Frob p n L] := sorry

variable (a : (𝔽_[p]^n)[X])

#check (algebraMap (𝔽_[p]^n)[X] L).toFun a

structure DrinfeldModule extends (𝔽_[p]^n)[X] →ₐ[(𝔽_[p]^n)] L[X; Frob p n L] where
  deriv : ∀ (a : (𝔽_[p]^n)[X]), (toFun a).coeff 0 = (algebraMap (𝔽_[p]^n)[X] L a)
  ne_trivial : ∃ (a : (𝔽_[p]^n)[X]), toFun a ≠ 0 -- TODO: fix ↑((algebraMap (𝔽_[p]^n)[X] L).toFun a)

end DrinfeldModule


--def Frob : 

