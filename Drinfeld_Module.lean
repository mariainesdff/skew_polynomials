--import Mathlib.NumberTheory.FunctionField
import Mathlib.FieldTheory.Finite.GaloisField
import SkewPolynomials

variable (p : ℕ) [h_prime : Fact p.Prime] (n : ℕ)


scoped[DrinfeldModule] notation:max "𝔽_["p"]^"n => GaloisField p n


open DrinfeldModule

#check 𝔽_[p]^n

def Frob : (𝔽_[p]^n) →+* 𝔽_[p]^n where
  toFun     := _
  map_one'  := _
  map_mul'  := _
  map_zero' := _
  map_add'  := _

namespace DrinfeldModule

end DrinfeldModule


--def Frob : 

