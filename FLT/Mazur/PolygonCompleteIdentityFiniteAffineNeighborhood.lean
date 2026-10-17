/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ClosedFiberAffineNeighborhood
public import FLT.Mazur.PolygonCompleteIdentityAdicSectionReduction

/-!
# Actual original affine inputs with a fixed target at every finite order

Choose neighborhoods in the unchanged complete input, using its closed fiber.
Surjectivity of the original nilpotent transitions makes the same target work
at every finite order, without discarding any nilpotent coordinates.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "P" => completeIdentityActionProduct K n h 0
local notation "X" => exactVeroneseProj K n h
local notation "j" m => completeIdentityFiniteInput K n h 0 m
local notation "f" m => completeIdentityFiniteScaling K n h m
local notation "d" m => completeIdentityFiniteRestriction K n h m

/-- A fixed original source/target pair that works at order zero works at every order. -/
theorem completeIdentityFiniteAffine_all (U : (P).Opens) (V : (X).Opens)
    (hUV : (j 0) ⁻¹ᵁ U ≤ (f 0) ⁻¹ᵁ V) (m : ℕ) :
    (j m) ⁻¹ᵁ U ≤ (f m) ⁻¹ᵁ V := by
  induction m with
  | zero => exact hUV
  | succ m ih =>
    intro y hy
    obtain ⟨z, rfl⟩ := (d m).surjective y
    have hj := congrArg (fun g ↦ g z) (completeIdentityFiniteRestriction_input K n h 0 m)
    have hf := congrArg (fun g ↦ g z) (completeIdentityFiniteRestriction_scaling K n h m)
    change (j (m + 1)) ((d m) z) ∈ U at hy
    change (f (m + 1)) ((d m) z) ∈ V
    rw [← Scheme.Hom.comp_apply, hf]
    apply ih
    change (j m) z ∈ U
    rwa [← Scheme.Hom.comp_apply, hj] at hy

/-- Every original closed input has actual affine neighborhoods valid at all finite orders. -/
theorem completeIdentityFiniteAffine_exists
    (z : PolygonInfinitesimal.scalingParameterFamily
      (Ring K 0) (parameter K 0) n h) :
    ∃ (U : (P).affineOpens) (V : (X).affineOpens),
      (j 0) z ∈ U.1 ∧ (f 0) z ∈ V.1 ∧
        ∀ m : ℕ, (j m) ⁻¹ᵁ U.1 ≤ (f m) ⁻¹ᵁ V.1 := by
  obtain ⟨U, V, hzU, hzV, hUV⟩ :=
    ClosedFiberAffineNeighborhood.exists_affine_pair (j 0) (f 0) z
  exact ⟨U, V, hzU, hzV, completeIdentityFiniteAffine_all K n h U.1 V.1 hUV⟩

/-- The selected source is an actual affine open of the original complete input. -/
def completeIdentityFiniteAffineSource
    (z : PolygonInfinitesimal.scalingParameterFamily
      (Ring K 0) (parameter K 0) n h) : (P).affineOpens :=
  (completeIdentityFiniteAffine_exists K n h z).choose

/-- A single actual original target affine works on the selected source at every order. -/
def completeIdentityFiniteAffineTarget
    (z : PolygonInfinitesimal.scalingParameterFamily
      (Ring K 0) (parameter K 0) n h) : (X).affineOpens :=
  (completeIdentityFiniteAffine_exists K n h z).choose_spec.choose

/-- The selected neighborhoods contain the original input and all its finite action images. -/
theorem completeIdentityFiniteAffine_spec
    (z : PolygonInfinitesimal.scalingParameterFamily
      (Ring K 0) (parameter K 0) n h) :
    (j 0) z ∈ (completeIdentityFiniteAffineSource K n h z).1 ∧
      (f 0) z ∈ (completeIdentityFiniteAffineTarget K n h z).1 ∧
      ∀ m : ℕ, (j m) ⁻¹ᵁ (completeIdentityFiniteAffineSource K n h z).1 ≤
        (f m) ⁻¹ᵁ (completeIdentityFiniteAffineTarget K n h z).1 :=
  (completeIdentityFiniteAffine_exists K n h z).choose_spec.choose_spec

end FLT.Mazur.PolygonInfinitesimalStages
