/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFlatTestLift
public import FLT.Mazur.SchemeFlatTargetFamilyReflection

/-!
# Descending actual polygon lifts from a flat family

Original polygon lifts on a jointly surjective flat family force the entire
graph over its original flat input to be invertible. The comparison retains
the unchanged cubic action and uses the actual graph pullbacks.
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
variable {T : Scheme} (v : T ⟶ completeIdentityActionProduct K n h 0) [Flat v]

/-- Original lifts on flat tests covering the input eliminate its full exceptional graph. -/
theorem completeIdentityActionFlatTestFamily_isIso {ι : Type*}
    (Y : ι → Scheme) (w : ∀ i, Y i ⟶ T) [∀ i, Flat (w i)]
    (hw : ∀ t : T, ∃ i, ∃ y : Y i, w i y = t)
    (F : ∀ i, Y i ⟶ exactVeroneseProj K n h)
    (hF : ∀ i, F i ≫ (c) = w i ≫ v ≫ (a)) :
    IsIso (pullback.snd (p) v) := by
  let _ : Flat (pullback.snd (p) v) :=
    SchemeFlatTargetFamilyReflection.flat_of_family (pullback.snd (p) v) Y w hw (by
      intro i
      let _ := completeIdentityActionFlatTestLift_graph_isIso K n h (w i ≫ v) (F i)
        (by simpa only [Category.assoc] using hF i)
      rw [← pullbackLeftPullbackSndIso_hom_snd (p) v (w i)]
      infer_instance)
  exact completeIdentityActionGraphBaseChange_isIso K n h v

/-- In particular such tests certify membership of an entire original input open. -/
theorem completeIdentityActionFlatTestFamily_le_flatOpen
    (U : (completeIdentityActionProduct K n h 0).Opens) {ι : Type*}
    (Y : ι → Scheme) (w : ∀ i, Y i ⟶ U.toScheme) [∀ i, Flat (w i)]
    (hw : ∀ t : U.toScheme, ∃ i, ∃ y : Y i, w i y = t)
    (F : ∀ i, Y i ⟶ exactVeroneseProj K n h)
    (hF : ∀ i, F i ≫ (c) = w i ≫ U.ι ≫ (a)) :
    U ≤ completeIdentityActionFlatOpen K n h := by
  let _ := completeIdentityActionFlatTestFamily_isIso K n h U.ι Y w hw F hF
  exact (SchemeFlatTargetOpen.le_locus_iff (p) U).mpr inferInstance

end FLT.Mazur.PolygonInfinitesimalStages
