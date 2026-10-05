/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.TateProjectionSurjective
public import FLT.GroupScheme.GenericPointSurjectivity
public import FLT.GroupScheme.PDivisibleCartierTateGalois

/-! # Actual Tate evaluations and nondegeneracy of the original inverse-limit pairing -/

@[expose] public noncomputable section
namespace ThreeAdicPlan.PDivisibleSystem
variable {R K : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsFractionRing R K] {p height : ℕ} [Fact p.Prime]
  (X : PDivisibleSystem R K p height)

/-- Faithfully flat integral reductions surject onto the original generic point groups. -/
theorem reduction_points_surjective {m n : ℕ} (h : m ≤ n) :
    Function.Surjective (genericHom (X.reduction h)) :=
  ModelHom.genericHom_surjective_of_injective _ (X.faithfullyFlat h).injective

/-- Every original finite point lifts to an actual coherent Tate vector. -/
theorem tateEval_surjective_unconditional (n : ℕ) : Function.Surjective (X.tateEval n) :=
  X.tateEval_surjective (fun h ↦ X.reduction_points_surjective h) n

variable [IsDomain R] [IsPrincipalIdealRing R] [CharZero K]

/-- Pairing against actual full Tate vectors separates dual Tate vectors. -/
theorem cartierTatePairing_separates {y z : X.CartierTate}
    (h : ∀ (x : X.tateSequences) n, X.cartierTatePairing y x n = X.cartierTatePairing z x n) :
    y = z := by
  apply X.cartierTateLevelPairing_separates
  intro n a
  obtain ⟨x, rfl⟩ := X.tateEval_surjective_unconditional n a
  exact h x n
end ThreeAdicPlan.PDivisibleSystem
