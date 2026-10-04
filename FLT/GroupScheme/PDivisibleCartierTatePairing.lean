/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PDivisibleCartierSystem
public import FLT.GroupScheme.PDivisibleTateModule
public import FLT.GroupScheme.RaynaudCartierPairingLaws

/-! # The actual dual Tate limit and its finite Cartier evaluations -/

@[expose] public noncomputable section
namespace ThreeAdicPlan.PDivisibleSystem
variable {R K : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
  [IsDomain R] [IsPrincipalIdealRing R] [IsFractionRing R K] [CharZero K]
  {p height : ℕ} [Fact p.Prime] (X : PDivisibleSystem R K p height)

/-- Coherent sequences on the actual dual levels, carrying their inherited p-adic module. -/
abbrev CartierTate := X.cartierDual.tateSequences

/-- Evaluation on a dual level is linear over the p-adic integers. -/
def cartierTateEval (n : ℕ) : X.CartierTate →ₗ[ℤ_[p]] (X.cartierDual.level n).Points :=
  X.cartierDual.tateEvalLinear n

/-- The limit evaluations use the original inclusion's transpose. -/
theorem cartierTateEval_transition {m n : ℕ} (h : m ≤ n) (y : X.CartierTate) :
    genericHom (X.inclusion h).cartierDual (X.cartierTateEval n y) =
      X.cartierTateEval m y := X.cartierDual.tateEval_reduction h y

/-- Evaluation of a dual Tate vector on an original finite-level point. -/
def cartierTateLevelPairing (n : ℕ) (y : X.CartierTate) (x : (X.level n).Points) :
    (AlgebraicClosure K)ˣ := (X.level n).cartierPairing (X.cartierTateEval n y) x

/-- Passing to a higher original level preserves the actual Cartier value. -/
theorem cartierTateLevelPairing_inclusion {m n : ℕ} (h : m ≤ n)
    (y : X.CartierTate) (x : (X.level m).Points) :
    X.cartierTateLevelPairing n y (genericHom (X.inclusion h) x) =
      X.cartierTateLevelPairing m y x := by
  unfold cartierTateLevelPairing
  exact ((X.inclusion h).cartierPairing_naturality (X.cartierTateEval n y) x).symm.trans
    (congrArg (fun z ↦ (X.level m).cartierPairing z x) (X.cartierTateEval_transition h y))

/-- Each finite value lies in the original p-power roots of unity. -/
theorem cartierTateLevelPairing_pow (n : ℕ) (y : X.CartierTate) (x : (X.level n).Points) :
    X.cartierTateLevelPairing n y x ^ (p ^ n) = 1 :=
  (X.level n).cartierPairing_pow_eq_one _ x _ (X.killed n x)

/-- Pair the two original inverse limits level by level. -/
def cartierTatePairing (y : X.CartierTate) (x : X.tateSequences) (n : ℕ) :
    (AlgebraicClosure K)ˣ := X.cartierTateLevelPairing n y (X.tateEval n x)

/-- The paired values obey the cyclotomic inverse-limit transition law. -/
theorem cartierTatePairing_transition {m n : ℕ} (h : m ≤ n)
    (y : X.CartierTate) (x : X.tateSequences) :
    X.cartierTatePairing y x n ^ (p ^ (n - m)) = X.cartierTatePairing y x m := by
  change (X.level n).cartierPairing (X.cartierTateEval n y) (X.tateEval n x) ^ _ = _
  erw [← FF.cartierPairing_nsmul_right]
  have he := congrArg (fun f ↦ genericHom f (X.tateEval n x)) (X.reduction_inclusion h)
  rw [genericHom_comp, FF.genericHom_multiply, X.tateEval_reduction h] at he
  rw [← he]
  exact X.cartierTateLevelPairing_inclusion h y (X.tateEval m x)

end ThreeAdicPlan.PDivisibleSystem
