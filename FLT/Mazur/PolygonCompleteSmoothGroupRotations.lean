/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteSmoothGroup

/-!
# Original cyclic rotations are translations in the full smooth group

The original cyclic markings multiply by addition of their labels. Translation
by each such marking retains exactly the original whole-family rotation after
the smooth inclusion. The zero chart is an actual homomorphism of groups.
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

attribute [local instance] completeSmoothGrpObj
open GroupObjectPointTranslation
local notation "π" => exactVeroneseProjToBase K n h

attribute [local irreducible] completeSmoothMul completePointOriginalBaseGroup

/-- The original identity-group chart embeds as a subgroup of the full smooth group. -/
instance completeIdentityChart_zero_isMonHom : IsMonHom (completeIdentityChart K n h 0 0) where
  one_hom := rfl
  mul_hom := by
    change μ[(G).X] ≫ completeIdentityChart K n h 0 0 =
      (completeIdentityChart K n h 0 0 ⊗ₘ completeIdentityChart K n h 0 0) ≫
        completeSmoothMul K n h
    rw [completeSmoothMul_chart, completeIdentityChartMul, zero_add]

/-- The original cyclic marking as a point of the constructed full smooth group. -/
def completeOriginalSmoothCyclicPoint (b : ZMod n) :
    𝟙_ (Over (Spec (.of (PowerSeries K)))) ⟶ (M) :=
  η[(G).X] ≫ completeIdentityChart K n h 0 b

/-- This point retains its unchanged original labeled section in the whole family. -/
@[reassoc] theorem completeOriginalSmoothCyclicPoint_inclusion (b : ZMod n) :
    (completeOriginalSmoothCyclicPoint K n h b).left ≫ (π).smoothLocus.ι =
      completeBaseMarking K n h (PolygonPinching.rotateIndex b (0 : Fin n)) :=
  completeIdentityChart_identity K n h 0 b

/-- The cyclic points multiply by addition of the original labels. -/
theorem completeOriginalSmoothCyclicPoint_add (b c : ZMod n) :
    completeOriginalSmoothCyclicPoint K n h (b + c) =
      completeOriginalSmoothCyclicPoint K n h b *
        completeOriginalSmoothCyclicPoint K n h c := by
  change _ = lift (η[(G).X] ≫ completeIdentityChart K n h 0 b)
    (η[(G).X] ≫ completeIdentityChart K n h 0 c) ≫ completeSmoothMul K n h
  rw [completeSmoothMul_evaluation]
  have he : η[(G).X] * η[(G).X] = η[(G).X] := by
    have ho : η[(G).X] = (1 : 𝟙_ (Over (Spec (.of (PowerSeries K)))) ⟶ (G).X) := by
      rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
    rw [ho, _root_.one_mul]
  rw [he]
  rfl

/-- The zero-labeled marking is the global smooth group identity. -/
theorem completeOriginalSmoothCyclicPoint_zero :
    completeOriginalSmoothCyclicPoint K n h 0 = 1 := by
  rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  rfl

/-- Translation by a cyclic marking shifts every original chart label. -/
@[reassoc] theorem completeIdentityChart_translation (a b : ZMod n) :
    completeIdentityChart K n h 0 b ≫
      translation (completeOriginalSmoothCyclicPoint K n h a) =
        completeIdentityChart K n h 0 (a + b) := by
  rw [comp_translation]
  change lift (toUnit (G).X ≫ (η[(G).X] ≫ completeIdentityChart K n h 0 a))
    (completeIdentityChart K n h 0 b) ≫ completeSmoothMul K n h = _
  rw [← Category.assoc]
  change lift ((1 : (G).X ⟶ (G).X) ≫ completeIdentityChart K n h 0 a)
    (completeIdentityChart K n h 0 b) ≫ completeSmoothMul K n h = _
  simpa only [Category.id_comp, _root_.one_mul] using
    completeSmoothMul_evaluation K n h a b (1 : (G).X ⟶ (G).X) (𝟙 (G).X)

attribute [local semireducible] completePointOriginalBaseGroup

/-- The actual smooth translation retains the unchanged original whole-family rotation. -/
@[reassoc] theorem completeOriginalSmooth_translation_rotation (a : ZMod n) :
    (translation (completeOriginalSmoothCyclicPoint K n h a)).left ≫ (π).smoothLocus.ι =
      (π).smoothLocus.ι ≫ completeRotation K n h a := by
  apply (C).hom_ext
  intro b
  change ZMod n at b
  change (completeIdentityChart K n h 0 b).left ≫
    (translation (completeOriginalSmoothCyclicPoint K n h a)).left ≫ _ = _
  rw [← Category.assoc]
  have he := congrArg Over.Hom.left (completeIdentityChart_translation K n h a b)
  change (completeIdentityChart K n h 0 b).left ≫
    (translation (completeOriginalSmoothCyclicPoint K n h a)).left = _ at he
  change _ = (completeIdentityChart K n h 0 b).left ≫
    (π).smoothLocus.ι ≫ completeRotation K n h a
  rw [he, completeIdentityChart_inclusion, completeIdentityChart_inclusion_assoc,
    ← completeRotation_add, add_comm a b]

end FLT.Mazur.PolygonInfinitesimalStages
