/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PDivisibleCotangentExactness
public import FLT.GroupScheme.FiniteFlatTangentNaturality

/-! # Torsion-valued tangents stabilize at the original finite level -/

@[expose] public noncomputable section
namespace ThreeAdicPlan.PDivisibleSystem
variable {R K M : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsFractionRing R K] {p height : ℕ} [Fact p.Prime]
  [AddCommGroup M] [Module R M] (X : PDivisibleSystem R K p height)

/-- Cotangent restriction induces the actual forward transition on functionals. -/
def cotangentStagePrecomp {r n : ℕ} (h : r ≤ n) :
    (X.LevelCotangent r →ₗ[R] M) →ₗ[R] (X.LevelCotangent n →ₗ[R] M) :=
  (LinearMap.llcomp R (X.LevelCotangent n) (X.LevelCotangent r) M).flip
    (X.cotangentRestriction h)

/-- Closedness of the original inclusion makes this transition injective. -/
theorem cotangentStagePrecomp_injective {r n : ℕ} (h : r ≤ n) :
    Function.Injective (X.cotangentStagePrecomp (M := M) h) :=
  (X.cotangentRestriction_surjective h).injective_linearMapComp_right

/-- Every p^r-torsion-valued functional at a later level descends to level r. -/
theorem cotangentStagePrecomp_surjective {r n : ℕ} (h : r ≤ n)
    (hM : ∀ a : M, p ^ r • a = 0) :
    Function.Surjective (X.cotangentStagePrecomp (M := M) h) := by
  intro f
  let e := (X.cotangentRestriction h).quotKerEquivOfSurjective
    (X.cotangentRestriction_surjective h)
  let d := (LinearMap.ker (X.cotangentRestriction h)).liftQ f (by
    intro a ha
    obtain ⟨b, rfl⟩ := (X.cotangentRestriction_eq_zero_iff h a).mp ha
    change f (p ^ r • b) = 0
    rw [map_nsmul, hM])
  refine ⟨d.comp e.symm.toLinearMap, ?_⟩
  ext a
  change d (e.symm (X.cotangentRestriction h a)) = f a
  have he : e (Submodule.Quotient.mk a) = X.cotangentRestriction h a := rfl
  rw [← he, e.symm_apply_apply]
  rfl

/-- Stabilization retains the original cotangent restriction as its forward map. -/
def cotangentStageEquiv {r n : ℕ} (h : r ≤ n) (hM : ∀ a : M, p ^ r • a = 0) :
    (X.LevelCotangent r →ₗ[R] M) ≃ₗ[R] (X.LevelCotangent n →ₗ[R] M) :=
  LinearEquiv.ofBijective (X.cotangentStagePrecomp h)
    ⟨X.cotangentStagePrecomp_injective h, X.cotangentStagePrecomp_surjective h hM⟩

/-- The same stabilization for actual Leibniz tangents. -/
def tangentStageEquiv {r n : ℕ} (h : r ≤ n) (hM : ∀ a : M, p ^ r • a = 0) :
    (X.level r).Tangent (M := M) ≃ₗ[R] (X.level n).Tangent (M := M) :=
  (X.level r).cotangentTangentEquiv.symm.trans
    ((X.cotangentStageEquiv h hM).trans (X.level n).cotangentTangentEquiv)

/-- Stabilization is the tangent map of the specified original inclusion. -/
theorem tangentStageEquiv_apply {r n : ℕ} (h : r ≤ n)
    (hM : ∀ a : M, p ^ r • a = 0) (d : (X.level r).Tangent (M := M)) :
    X.tangentStageEquiv h hM d = (X.inclusion h).tangentMap d := by
  obtain ⟨f, rfl⟩ := (X.level r).cotangentTangentEquiv.surjective d
  rw [ModelHom.cotangentTangent_naturality]
  change (X.level n).cotangentTangentEquiv
    (X.cotangentStagePrecomp h ((X.level r).cotangentTangentEquiv.symm
      ((X.level r).cotangentTangentEquiv f))) = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

end ThreeAdicPlan.PDivisibleSystem
