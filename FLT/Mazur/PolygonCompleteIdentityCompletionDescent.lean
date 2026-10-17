/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFlatTestLift
public import FLT.Mazur.SchemeAdicCompletionFlatDescent

/-!
# Complete-input graph coverage from actual completed and generic polygon lifts

For any flat affine input in the original product, genuine polygon maps on its
parameter completion and generic localization suffice. They need only retain
the prescribed cubic equation; the original full graph supplies their descent.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "p" => completeIdentityActionGraphProjection K n h
local notation "c" => completePointToIntegralCubic K n h (0 : Fin n)
local notation "a" => completeIdentityActionTarget K n h (0 : Fin n)
variable {R : Type} [CommRing R] [IsNoetherianRing R]
  (v : Spec (.of R) ⟶ completeIdentityActionProduct K n h 0) [Flat v] (t : R)
local notation "d" => Spec.map (CommRingCat.ofHom
  (algebraMap R (AdicCompletion (Ideal.span (Set.singleton t)) R)))
local notation "g" => Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away t)))

/-- Completed and generic original polygon lifts give an inverse on the full affine input. -/
theorem completeIdentityActionCompletion_graph_isIso
    (F : Spec (.of (AdicCompletion (Ideal.span {t}) R)) ⟶ exactVeroneseProj K n h)
    (hF : F ≫ (c) = (d) ≫ v ≫ (a))
    (G : Spec (.of (Localization.Away t)) ⟶ exactVeroneseProj K n h)
    (hG : G ≫ (c) = (g) ≫ v ≫ (a)) :
    IsIso (pullback.snd (p) v) := by
  let _ : Flat (d) := Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  let _ : Flat (g) := Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  let _ := completeIdentityActionFlatTestLift_graph_isIso K n h ((d) ≫ v) F
    (by simpa only [Category.assoc] using hF)
  let _ := completeIdentityActionFlatTestLift_graph_isIso K n h ((g) ≫ v) G
    (by simpa only [Category.assoc] using hG)
  let _ : Flat (pullback.snd (pullback.snd (p) v) (d)) := by
    rw [← pullbackLeftPullbackSndIso_hom_snd (p) v (d)]
    infer_instance
  let _ : Flat (pullback.snd (pullback.snd (p) v) (g)) := by
    rw [← pullbackLeftPullbackSndIso_hom_snd (p) v (g)]
    infer_instance
  let _ := SchemeAdicCompletionFlatDescent.flat_of_completion_and_away
    (pullback.snd (p) v) t
  exact completeIdentityActionGraphBaseChange_isIso K n h v

end FLT.Mazur.PolygonInfinitesimalStages
