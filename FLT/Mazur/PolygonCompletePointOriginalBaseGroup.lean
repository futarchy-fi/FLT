/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointIdentityGroup

/-!
# The constructed identity group over the unchanged power-series spectrum

Transport the existing group along the specified coefficient-spectrum
isomorphism. The underlying open, its inclusion, and its original marking
are retained; the base is now literally Spec K[[X]].
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] completePointWeierstrassCurve completePointToIntegralCubic
  exactVeroneseProj exactVeroneseProjToBase
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "S₀" => Spec (CommRingCat.of (PowerSeries K))
local notation "U" => completePointIdentityOpen K n h i
local notation "F" => Over.map (inv (Scheme.toSpecΓ (S₀)))

/-- The specified coefficient identification preserves the cartesian group operations. -/
abbrev completePointOriginalBaseBraided : (F).Braided := .ofChosenFiniteProducts _
attribute [local instance] completePointOriginalBaseBraided

/-- The constructed identity group, now over the literal original power-series spectrum. -/
def completePointOriginalBaseGroup : CommGrp (Over S₀) :=
  (F).mapCommGrp.obj (completePointIdentityGroup K n h i)

/-- Coefficient transport leaves the underlying original identity open unchanged. -/
theorem completePointOriginalBaseGroup_carrier :
    (completePointOriginalBaseGroup K n h i).X.left = (U).toScheme := rfl

/-- Its structural map is precisely the restriction of the original family. -/
theorem completePointOriginalBaseGroup_structure :
    (completePointOriginalBaseGroup K n h i).X.hom =
      (U).ι ≫ exactVeroneseProjToBase K n h := by
  change ((U).ι ≫ completePointToIntegralCubic K n h i ≫
    WeierstrassIntegralChart.integralCurveStructure (completePointWeierstrassCurve K n h i)) ≫
      inv (S₀).toSpecΓ = _
  simp only [Category.assoc, completePointToIntegralCubic_over_assoc,
    IsIso.hom_inv_id, Category.comp_id]

/-- The coefficient transport's unit comparison is the original specified base isomorphism. -/
theorem completePointOriginalBase_unitComparison :
    (Functor.LaxMonoidal.ε (F)).left = (S₀).toSpecΓ := by
  have H := (Functor.LaxMonoidal.ε (F)).w
  change (Functor.LaxMonoidal.ε (F)).left ≫ (𝟙 _ ≫ inv (S₀).toSpecΓ) = 𝟙 _ at H
  rw [Category.id_comp] at H
  apply (cancel_mono (inv (S₀).toSpecΓ)).mp
  rw [H, IsIso.hom_inv_id]

/-- The group identity over the original base is exactly the original lifted marking. -/
theorem completePointOriginalBaseGroup_identity :
    (η[(completePointOriginalBaseGroup K n h i).X]).left =
      completePointIdentityMarking K n h i := by
  change (Functor.LaxMonoidal.ε (F)).left ≫
    (η[(completePointIdentityGroup K n h i).X]).left = _
  rw [completePointOriginalBase_unitComparison]
  change (S₀).toSpecΓ ≫
    (let _ := completePointIdentityCommGrp K n h i
     (η[completePointIdentityOver K n h i]).left) = _
  rw [completePointIdentityCommGrp_identity, IsIso.hom_inv_id_assoc]

end FLT.Mazur.PolygonInfinitesimalStages
