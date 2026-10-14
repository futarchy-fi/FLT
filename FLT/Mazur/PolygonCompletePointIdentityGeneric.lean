/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointIdentityClosedTorus

/-!
# The entire nonzero-parameter fiber lies in the original identity open

The original field comparison is an isomorphism onto the changed cubic.
Smoothness of that fiber and flat base change therefore put every one of
its points in the full identity open, for every choice of retained component.
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
local notation "f" => exactVeroneseProjToBase K n h
local notation "g" => completePointToIntegralCubic K n h i
local notation "c" => integralCurveStructure (completePointWeierstrassCurve K n h i)
local notation "U" => completePointIdentityOpen K n h i

/-- Every nonzero-parameter field square is contained in the full original identity open. -/
theorem completePointIdentityOpen_field_preimage
    (L : Type) [Field L] (a : PowerSeries K →+* L) (ha : a PowerSeries.X ≠ 0)
    {Y : Scheme} (p : Y ⟶ exactVeroneseProj K n h) (q : Y ⟶ Spec (.of L))
    (hs : IsPullback p q (f) (Spec.map (CommRingCat.ofHom a))) :
    p ⁻¹ᵁ (U) = ⊤ := by
  let s := Spec.map (CommRingCat.ofHom a)
  let _ := completePointToCubicBaseChange_isIso_of_parameter_ne_zero K n h L a ha p q hs i
  let _ := completeCartesianField_relativeDimension K n h L a ha p q hs
  let _ : Smooth q := SmoothOfRelativeDimension.smooth 1 q
  change p ⁻¹ᵁ ((g) ⁻¹ᵁ (c).smoothLocus) = ⊤
  rw [← Scheme.Hom.comp_preimage, ← completePointToCubicBaseChange_fst K n h s p q hs i,
    Scheme.Hom.comp_preimage, Scheme.Hom.preimage_smoothLocus_baseChange,
    Scheme.Hom.preimage_smoothLocus_eq]
  simp only [completePointToCubicBaseChange_snd, Scheme.Hom.smoothLocus_eq_top]

/-- Every original point away from the parameter divisor lies in the entire identity open. -/
theorem completePointIdentityOpen_mem_of_parameter_notMem
    (x : exactVeroneseProj K n h) (hx : PowerSeries.X ∉ ((f) x).asIdeal) : x ∈ (U) := by
  let z := (f) x
  let s := (S₀).fromSpecResidueField z
  let a := (Spec.preimage s).hom
  have he : Spec.map (CommRingCat.ofHom a) = s := Spec.map_preimage s
  have ha : a PowerSeries.X ≠ 0 := by
    intro hz
    apply hx
    have hz' : Spec.map (CommRingCat.ofHom a) (default : Spec ((S₀).residueField z)) = z := by
      rw [he]
      exact Scheme.fromSpecResidueField_apply _ _
    change PowerSeries.X ∈ z.asIdeal
    rw [← hz']
    change a PowerSeries.X ∈ (default : Spec ((S₀).residueField z)).asIdeal
    rw [hz]
    exact Ideal.zero_mem _
  let p := pullback.fst (f) (Spec.map (CommRingCat.ofHom a))
  let q := pullback.snd (f) (Spec.map (CommRingCat.ofHom a))
  have hr : x ∈ Set.range p := by
    rw [Scheme.Pullback.range_fst]
    refine ⟨default, ?_⟩
    rw [he]
    exact Scheme.fromSpecResidueField_apply _ _
  obtain ⟨y, hy⟩ := hr
  have H := completePointIdentityOpen_field_preimage K n h i
    ((S₀).residueField z) a ha p q (.of_hasPullback _ _)
  have hm : p y ∈ (U) := H.ge (show y ∈ ⊤ from trivial)
  rwa [hy] at hm

end FLT.Mazur.PolygonInfinitesimalStages
