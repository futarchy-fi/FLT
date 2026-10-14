/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointGenericNeighborhood

/-!
# Every nonzero-parameter cubic point has an unchanged neighborhood

Use the actual residue field at the point of the original coefficient base.
Its canonical preimmersion preserves the point fiber, so the original
nonzero-parameter field comparison applies at every such cubic point.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "S₀" => Spec (CommRingCat.of (PowerSeries K))
local notation "W" => completePointWeierstrassCurve K n h i
local notation "g" => completePointToIntegralCubic K n h i
local notation "c" => integralCurveStructure (W)

/-- The original cubic over the unchanged complete power-series spectrum. -/
def completePointCubicOriginalBase : integralCurve (W) ⟶ S₀ :=
  (c) ≫ inv (S₀).toSpecΓ

/-- The original coefficient map is retained by the complete-base cubic contraction. -/
@[reassoc] theorem completePointToIntegralCubic_originalBase :
    (g) ≫ completePointCubicOriginalBase K n h i = exactVeroneseProjToBase K n h := by
  rw [completePointCubicOriginalBase, completePointToIntegralCubic_over_assoc,
    IsIso.hom_inv_id, Category.comp_id]

/-- At any original base residue point avoiding the parameter, the full map is unchanged nearby. -/
theorem completePointToIntegralCubic_exists_isIso_parameter_notMem
    (y : integralCurve (W))
    (hy : PowerSeries.X ∉ (completePointCubicOriginalBase K n h i y).asIdeal) :
    ∃ U : (integralCurve (W)).Opens, y ∈ U ∧ IsIso ((g) ∣_ U) := by
  let z := completePointCubicOriginalBase K n h i y
  let s := (S₀).fromSpecResidueField z
  let a := (Spec.preimage s).hom
  have he : Spec.map (CommRingCat.ofHom a) = s := Spec.map_preimage s
  have ha : a PowerSeries.X ≠ 0 := by
    intro hz
    apply hy
    have hz' : Spec.map (CommRingCat.ofHom a) (default : Spec ((S₀).residueField z)) = z := by
      rw [he]
      exact Scheme.fromSpecResidueField_apply _ _
    change PowerSeries.X ∈ z.asIdeal
    rw [← hz']
    change a PowerSeries.X ∈ (default : Spec ((S₀).residueField z)).asIdeal
    rw [hz]
    exact Ideal.zero_mem _
  let _ : IsPreimmersion (Spec.map (CommRingCat.ofHom a)) := he.symm ▸ inferInstanceAs
    (IsPreimmersion s)
  have hr : y ∈ Set.range (pullback.fst (c)
      (Spec.map (CommRingCat.ofHom a) ≫ (S₀).toSpecΓ)) := by
    rw [Scheme.Pullback.range_fst]
    refine ⟨default, ?_⟩
    rw [he]
    change (S₀).toSpecΓ (s default) = (c) y
    rw [Scheme.fromSpecResidueField_apply]
    change (inv (S₀).toSpecΓ ≫ (S₀).toSpecΓ) ((c) y) = (c) y
    rw [IsIso.inv_hom_id]
    rfl
  obtain ⟨y', hy'⟩ := hr
  have H := completePointToIntegralCubic_exists_isIso_generic K n h i
    ((S₀).residueField z) a ha y'
  simpa only [hy'] using H

end FLT.Mazur.PolygonInfinitesimalStages
