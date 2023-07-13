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

def AddMonoidAlgebra.mul' (φ : R →+* R) (f g : AddMonoidAlgebra R ℕ) :
  (AddMonoidAlgebra R ℕ) :=
  f.sum fun a₁ b₁ => g.sum fun a₂ b₂ => single (a₁ + a₂) (b₁ * (φ^[a₁] b₂))

private def AddMonoidAlgebra.pow' (φ : R →+* R) : ℕ → (AddMonoidAlgebra R ℕ) → (AddMonoidAlgebra R ℕ) 
  | 0, _ => 1
  | n + 1, f => AddMonoidAlgebra.mul' φ f (AddMonoidAlgebra.pow' φ n f)

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

theorem AddMonoidAlgebra.mul'_def (φ : R →+* R) {f g : AddMonoidAlgebra R ℕ} :
    AddMonoidAlgebra.mul' φ f g = (f.sum fun a₁ b₁ => g.sum fun a₂ b₂ => single (a₁ + a₂) (b₁ * (φ^[a₁] b₂))) :=
  rfl

instance smulZeroClass {S : Type _} [SMulZeroClass S R] : SMulZeroClass S R[X;φ] where
  smul r p := ⟨r • p.toFinsupp⟩
  smul_zero a := congr_arg ofFinsupp (smul_zero a)

-- to avoid a bug in the `ring` tactic
instance (priority := 1) pow : Pow R[X;φ] ℕ where pow p n := npowRec n p

@[simp]
theorem ofFinsupp_zero : (⟨0⟩ : R[X;φ]) = 0 :=
  rfl

@[simp]
theorem ofFinsupp_one : (⟨1⟩ : R[X;φ]) = 1 :=
  rfl

@[simp]
theorem ofFinsupp_add {a b} : (⟨a + b⟩ : R[X;φ]) = ⟨a⟩ + ⟨b⟩ :=
  show _ = add _ _ by rw [add_def]

@[simp]
theorem ofFinsupp_neg {S : Type u} [Ring S] {φ : S →+* S} {a} : (⟨-a⟩ : S[X;φ]) = -⟨a⟩ :=
  show _ = neg _ by rw [neg_def]

@[simp]
theorem ofFinsupp_sub {S : Type u} [Ring S] {φ : S →+* S} {a b} : (⟨a - b⟩ : S[X;φ]) = ⟨a⟩ - ⟨b⟩ := by
  rw [sub_eq_add_neg, ofFinsupp_add, ofFinsupp_neg]
  rfl

@[simp]
theorem ofFinsupp_mul (a b) : (⟨AddMonoidAlgebra.mul' φ a b⟩ : R[X;φ]) = ⟨a⟩ * ⟨b⟩ := 
  show _ = mul _ _ by rw [mul_def]

@[simp]
theorem ofFinsupp_smul {S : Type _} [SMulZeroClass S R] (a : S) (b) :
    (⟨a • b⟩ : R[X;φ]) = (a • ⟨b⟩ : R[X;φ]) :=
  rfl

@[simp]
theorem ofFinsupp_pow (a) (n : ℕ) : (⟨AddMonoidAlgebra.pow' φ n a⟩ : R[X;φ]) = ⟨a⟩ ^ n := by
  change _ = npowRec n _
  induction n with
  | zero        => simp [npowRec]; rfl
  | succ n n_ih => simp [npowRec, pow_succ]; rw [<- n_ih, <- ofFinsupp_mul]; rfl

@[simp]
theorem toFinsupp_zero : (0 : R[X;φ]).toFinsupp = 0 :=
  rfl

@[simp]
theorem toFinsupp_one : (1 : R[X;φ]).toFinsupp = 1 :=
  rfl

@[simp]
theorem toFinsupp_add (a b : R[X;φ]) : (a + b).toFinsupp = a.toFinsupp + b.toFinsupp := by
  cases a
  cases b
  rw [← ofFinsupp_add]

@[simp]
theorem toFinsupp_neg {S : Type u} [Ring S] {φ : S →+* S} (a : S[X;φ]) : (-a).toFinsupp = -a.toFinsupp := by
  cases a
  rw [← ofFinsupp_neg]

@[simp]
theorem toFinsupp_sub {S : Type u} [Ring S] {φ : S →+* S} (a b : S[X;φ]) :
    (a - b).toFinsupp = a.toFinsupp - b.toFinsupp := by
  rw [sub_eq_add_neg, ← toFinsupp_neg, ← toFinsupp_add]
  rfl

@[simp]
theorem toFinsupp_mul (a b : R[X;φ]) : (a * b).toFinsupp = AddMonoidAlgebra.mul' φ a.toFinsupp b.toFinsupp := by
  cases a
  cases b
  rw [← ofFinsupp_mul]


@[simp]
theorem toFinsupp_smul {S : Type _} [SMulZeroClass S R] (a : S) (b : R[X;φ]) :
    (a • b).toFinsupp = a • b.toFinsupp :=
  rfl

@[simp]
theorem toFinsupp_pow (a : R[X;φ]) (n : ℕ) : (a ^ n).toFinsupp = AddMonoidAlgebra.pow' φ n a.toFinsupp := by
  cases a
  rw [← ofFinsupp_pow]

theorem _root_.IsSMulRegular.polynomial {S : Type _} [Monoid S] [DistribMulAction S R] {a : S}
    (ha : IsSMulRegular R a) : IsSMulRegular R[X;φ] a
  | ⟨_x⟩, ⟨_y⟩, h => congr_arg _ <| ha.finsupp (SkewPolynomial.ofFinsupp.inj h)

theorem toFinsupp_injective : Function.Injective (toFinsupp : R[X;φ] → AddMonoidAlgebra _ _) :=
  fun ⟨_x⟩ ⟨_y⟩ => congr_arg _

@[simp]
theorem toFinsupp_inj {a b : R[X;φ]} : a.toFinsupp = b.toFinsupp ↔ a = b :=
  toFinsupp_injective.eq_iff

@[simp]
theorem toFinsupp_eq_zero {a : R[X;φ]} : a.toFinsupp = 0 ↔ a = 0 := by
  rw [← toFinsupp_zero, toFinsupp_inj]

@[simp]
theorem toFinsupp_eq_one {a : R[X;φ]} : a.toFinsupp = 1 ↔ a = 1 := by
  rw [← toFinsupp_one, toFinsupp_inj]

/-- A more convenient spelling of `Polynomial.ofFinsupp.injEq` in terms of `Iff`. -/
theorem ofFinsupp_inj {a b} : (⟨a⟩ : R[X;φ]) = ⟨b⟩ ↔ a = b :=
  iff_of_eq (ofFinsupp.injEq _ _)

@[simp]
theorem ofFinsupp_eq_zero {a} : (⟨a⟩ : R[X;φ]) = 0 ↔ a = 0 := by
  rw [← ofFinsupp_zero, ofFinsupp_inj]

@[simp]
theorem ofFinsupp_eq_one {a} : (⟨a⟩ : R[X;φ]) = 1 ↔ a = 1 := by rw [← ofFinsupp_one, ofFinsupp_inj]

instance inhabited : Inhabited R[X;φ] :=
  ⟨0⟩

instance natCast : NatCast R[X;φ] :=
  ⟨fun n => SkewPolynomial.ofFinsupp n⟩

instance AddCommMonoid : AddCommMonoid R[X;φ] := 
  Function.Injective.addCommMonoid toFinsupp toFinsupp_injective
  toFinsupp_zero toFinsupp_add (fun _ _ => toFinsupp_smul _ _)

instance Semiring : Semiring R[X;φ] where
  zero := 0
  one  := 1
  add  := (· + ·)
  mul  := (· * ·)
  add_assoc := AddCommMonoid.add_assoc
  zero_add := AddCommMonoid.zero_add
  add_zero := AddCommMonoid.add_zero
  nsmul_zero := AddCommMonoid.nsmul_zero
  nsmul_succ := AddCommMonoid.nsmul_succ
  add_comm := AddCommMonoid.add_comm
  left_distrib := sorry
  right_distrib := sorry
  zero_mul := by 
    intro a
    rw [← toFinsupp_inj, toFinsupp_mul, AddMonoidAlgebra.mul'_def, toFinsupp_zero, sum_zero_index]
  mul_zero := sorry
  mul_assoc := sorry
  one_mul := sorry
  mul_one := sorry
  natCast := sorry
  natCast_zero := sorry
  natCast_succ := sorry
