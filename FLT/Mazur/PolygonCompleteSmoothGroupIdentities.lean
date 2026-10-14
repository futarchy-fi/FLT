/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteSmoothMultiplication

/-!
# Chart evaluation and identities for the global smooth multiplication

Evaluation on arbitrary relative test morphisms retains the original
identity-group product. Units, commutativity and inverse laws follow on the
entire original smooth locus by its proved chart covers.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj GrpObj
open CartesianMonoidalCategory
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic completeRotation
attribute [local instance] exactVeroneseProjToBase_lfp
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "G" => completePointOriginalBaseGroup K n h (0 : Fin n)
local notation "M" => completeOriginalSmoothOver K n h
local notation "C" => completeIdentityChartCover K n h (0 : Fin n)

attribute [local irreducible] completeSmoothMul completePointOriginalBaseGroup

/-- Evaluation of global multiplication in any two original charts. -/
theorem completeSmoothMul_evaluation {T : Over (Spec (.of (PowerSeries K)))}
    (b c : ZMod n) (x y : T ⟶ (G).X) :
    lift (x ≫ completeIdentityChart K n h 0 b) (y ≫ completeIdentityChart K n h 0 c) ≫
      completeSmoothMul K n h = (x * y) ≫ completeIdentityChart K n h 0 (b + c) := by
  rw [← lift_map, Category.assoc, completeSmoothMul_chart]
  change lift x y ≫ μ[(G).X] ≫ completeIdentityChart K n h 0 (b + c) = _
  rw [← Category.assoc]
  rfl

/-- The original identity marking, viewed in the entire smooth scheme. -/
def completeSmoothOne : 𝟙_ (Over (Spec (.of (PowerSeries K)))) ⟶ (M) :=
  η[(G).X] ≫ completeIdentityChart K n h 0 0

/-- Relative morphisms out of the full smooth scheme are detected on its original charts. -/
theorem completeSmooth_hom_ext {Y : Over (Spec (.of (PowerSeries K)))}
    (f g : (M) ⟶ Y) (he : ∀ b : ZMod n,
      completeIdentityChart K n h 0 b ≫ f = completeIdentityChart K n h 0 b ≫ g) : f = g := by
  apply Over.OverMorphism.ext
  apply (C).hom_ext
  intro b
  exact congrArg Over.Hom.left (he b)

/-- The global original identity is a left unit on the whole smooth locus. -/
theorem completeSmoothMul_left_unit :
    lift (toUnit (M) ≫ completeSmoothOne K n h) (𝟙 (M)) ≫
      completeSmoothMul K n h = 𝟙 (M) := by
  apply completeSmooth_hom_ext K n h
  intro b
  rw [comp_lift_assoc, Category.comp_id, completeSmoothOne, ← Category.assoc,
    comp_toUnit]
  rw [← Category.assoc]
  change lift ((1 : (G).X ⟶ (G).X) ≫ completeIdentityChart K n h 0 0)
    (completeIdentityChart K n h 0 b) ≫ _ = _
  simpa only [Category.id_comp, _root_.one_mul, zero_add] using
    completeSmoothMul_evaluation K n h 0 b (1 : (G).X ⟶ (G).X) (𝟙 (G).X)

/-- The global original identity is a right unit on the whole smooth locus. -/
theorem completeSmoothMul_right_unit :
    lift (𝟙 (M)) (toUnit (M) ≫ completeSmoothOne K n h) ≫
      completeSmoothMul K n h = 𝟙 (M) := by
  apply completeSmooth_hom_ext K n h
  intro b
  rw [comp_lift_assoc, Category.comp_id, completeSmoothOne, ← Category.assoc,
    comp_toUnit]
  rw [← Category.assoc]
  change lift (completeIdentityChart K n h 0 b)
    ((1 : (G).X ⟶ (G).X) ≫ completeIdentityChart K n h 0 0) ≫ _ = _
  simpa only [Category.id_comp, _root_.mul_one, add_zero] using
    completeSmoothMul_evaluation K n h b 0 (𝟙 (G).X) (1 : (G).X ⟶ (G).X)

/-- Global multiplication is commutative on the full relative product. -/
theorem completeSmoothMul_comm :
    (β_ (M) (M)).hom ≫ completeSmoothMul K n h = completeSmoothMul K n h := by
  apply completeSmoothProduct_hom_ext K n h
  intro b c
  rw [BraidedCategory.braiding_naturality_assoc, completeSmoothMul_chart]
  exact (completeIdentityChartMul_comm K n h 0 b c).trans
    (completeSmoothMul_chart K n h b c).symm

/-- The independently glued inversion is a left inverse everywhere. -/
theorem completeSmoothMul_left_inv :
    lift (completeSmoothInv K n h) (𝟙 (M)) ≫ completeSmoothMul K n h =
      toUnit (M) ≫ completeSmoothOne K n h := by
  apply completeSmooth_hom_ext K n h
  intro b
  rw [comp_lift_assoc, completeSmoothInv_chart, Category.comp_id]
  rw [completeIdentityChartInv]
  have he := completeSmoothMul_evaluation K n h (-b) b (ι[(G).X]) (𝟙 (G).X)
  simp only [Category.id_comp] at he
  rw [he]
  have hi : ι[(G).X] = (𝟙 (G).X)⁻¹ := by
    rw [Hom.inv_def, Category.id_comp]
  rw [hi]
  rw [inv_mul_cancel, neg_add_cancel, completeSmoothOne, ← Category.assoc, comp_toUnit]
  rfl

/-- The independently glued inversion is a right inverse everywhere. -/
theorem completeSmoothMul_right_inv :
    lift (𝟙 (M)) (completeSmoothInv K n h) ≫ completeSmoothMul K n h =
      toUnit (M) ≫ completeSmoothOne K n h := by
  rw [← completeSmoothMul_comm, ← Category.assoc, lift_braiding_hom]
  exact completeSmoothMul_left_inv K n h

end FLT.Mazur.PolygonInfinitesimalStages
