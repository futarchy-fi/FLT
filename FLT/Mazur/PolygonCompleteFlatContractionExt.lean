/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteGenericMapIdentity

/-!
# The original contraction detects maps from flat original-base test schemes

The contraction is invertible on the generic fiber. Schematic density then
proves uniqueness on flat test schemes, even when images meet contracted nodes.
This is a uniqueness result and supplies no extension morphism at those nodes.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "π" => exactVeroneseProjToBase K n h
local notation "c" => completePointToIntegralCubic K n h i
local notation "U" => completePointIdentityOpen K n h i

/-- The full contraction detects maps from every flat test scheme over the unchanged base. -/
theorem completeFlat_contraction_ext {T : Scheme}
    (t : T ⟶ Spec (.of (PowerSeries K))) [Flat t]
    (f g : T ⟶ exactVeroneseProj K n h)
    (hf : f ≫ (π) = t) (hg : g ≫ (π) = t)
    (hc : f ≫ (c) = g ≫ (c)) : f = g := by
  let L := FractionRing (PowerSeries K)
  let a := algebraMap (PowerSeries K) L
  have ha : a PowerSeries.X ≠ 0 := by
    intro hz
    exact PowerSeries.X_ne_zero ((IsFractionRing.injective (PowerSeries K) L)
      (hz.trans (map_zero a).symm))
  let b := Spec.map (CommRingCat.ofHom a)
  let r := pullback.fst t b
  let q := pullback.snd t b
  have hf' : (r ≫ f) ≫ (π) = q ≫ b := by
    rw [Category.assoc, hf]
    exact pullback.condition
  have hg' : (r ≫ g) ≫ (π) = q ≫ b := by
    rw [Category.assoc, hg]
    exact pullback.condition
  let f' := completeGenericMapToIdentity K n h i L a ha (r ≫ f) q hf'
  let g' := completeGenericMapToIdentity K n h i L a ha (r ≫ g) q hg'
  have hfi : f' ≫ (U).ι = r ≫ f := completeGenericMapToIdentity_inclusion _ _ _ _ _ _ _ _ _ _
  have hgi : g' ≫ (U).ι = r ≫ g := completeGenericMapToIdentity_inclusion _ _ _ _ _ _ _ _ _ _
  have he : f' = g' := by
    apply (cancel_mono (completePointSmoothCubicIso K n h i).hom).mp
    apply (cancel_mono
      (WeierstrassIntegralChart.integralSmoothOpen (completePointWeierstrassCurve K n h i)).ι).mp
    simp only [Category.assoc, completePointSmoothCubicIso_inclusion]
    rw [← Category.assoc f', hfi, ← Category.assoc g', hgi, Category.assoc, hc,
      Category.assoc]
  apply completeFlat_toComplete_generic_ext K n h L t f g (hf.trans hg.symm)
  change r ≫ f = r ≫ g
  rw [← hfi, ← hgi, he]

end FLT.Mazur.PolygonInfinitesimalStages
