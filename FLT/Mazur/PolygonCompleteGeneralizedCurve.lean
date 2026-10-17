/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteGeometricRotations
public import FLT.Mazur.PolygonCompleteWholeActionLaws
public import FLT.Mazur.PolygonCompleteGenusOneFamily

/-!
# The original complete polygon as a generalized elliptic curve

The constructed full smooth group and whole action assemble with the classified
family and the proved geometric rotations. The underlying curve and inclusion
are the original schemes over the original complete coefficient ring.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
open CartesianMonoidalCategory
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
attribute [local instance] exactVeroneseProjToBase_lfp completeSmoothGrpObj
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "M" => completeOriginalSmoothOver K n h
local notation "X" => completeOriginalWholeOver K n h

/-- The original full action satisfies the monoidal identity law. -/
theorem completeWholeAction_one :
    η[(M)] ▷ (X) ≫ completeWholeAction K n h = (λ_ (X)).hom := by
  apply (cancel_epi (λ_ (X)).inv).mp
  have he : (λ_ (X)).inv = lift (toUnit (X)) (𝟙 (X)) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp only
      [leftUnitor_inv_fst, leftUnitor_inv_snd, lift_fst, lift_snd]
  rw [he, lift_whiskerRight_assoc, lift_leftUnitor_hom]
  exact completeWholeAction_unit K n h

/-- The original complete polygon, with its constructed full smooth group and whole action. -/
def completeGeneralizedCurve : GeneralizedEllipticCurve (Spec (.of (PowerSeries K))) where
  curve := (X)
  family := exactVeroneseProjToBase_classifiedGenusOneFamily K n h
  group := (M)
  smoothIso := Iso.refl _
  act := completeWholeAction K n h
  unit_act := completeWholeAction_one K n h
  assoc_act := completeWholeAction_assoc K n h
  restriction := by
    change (M) ◁ completeWholeSmoothInclusion K n h ≫ completeWholeAction K n h =
      completeSmoothMul K n h ≫ completeWholeSmoothInclusion K n h
    simpa only [tensorHom_def, id_whiskerRight, Category.id_comp] using
      completeWholeAction_smooth K n h
  rotations := completeWholeAction_geometricRotations K n h

/-- The generalized curve retains the actual original full smooth-open inclusion. -/
theorem completeGeneralizedCurve_inclusion :
    (completeGeneralizedCurve K n h).inclusion = completeWholeSmoothInclusion K n h := by
  let _ : LocallyOfFinitePresentation (X).hom := exactVeroneseProjToBase_lfp K n h
  change 𝟙 _ ≫ curveSmoothInclusion (X) = _
  rw [Category.id_comp]
  rfl

/-- The generalized curve uses the original entire action, including the nodes. -/
theorem completeGeneralizedCurve_action :
    (completeGeneralizedCurve K n h).act = completeWholeAction K n h := rfl

end FLT.Mazur.PolygonInfinitesimalStages
