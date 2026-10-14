/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteSmoothGroupIdentities
public import FLT.Mazur.PolygonCompleteSmoothTripleCover

/-!
# The commutative group on the entire original smooth polygon

Triple chart evaluation proves associativity globally. Together with the
already proved units and inverses this constructs the full group object;
no group structure on the full smooth locus is supplied as input.
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

/-- Associativity on any three original chart presentations over any relative test object. -/
theorem completeSmoothMul_associative_evaluation {T : Over (Spec (.of (PowerSeries K)))}
    (b c d : ZMod n) (x y z : T ⟶ (G).X) :
    lift (lift (x ≫ completeIdentityChart K n h 0 b)
      (y ≫ completeIdentityChart K n h 0 c) ≫ completeSmoothMul K n h)
      (z ≫ completeIdentityChart K n h 0 d) ≫ completeSmoothMul K n h =
    lift (x ≫ completeIdentityChart K n h 0 b)
      (lift (y ≫ completeIdentityChart K n h 0 c)
      (z ≫ completeIdentityChart K n h 0 d) ≫ completeSmoothMul K n h) ≫
      completeSmoothMul K n h := by
  simp only [completeSmoothMul_evaluation, _root_.mul_assoc, add_assoc]

/-- Global multiplication is associative on the entire original relative triple product. -/
theorem completeSmoothMul_assoc :
    (completeSmoothMul K n h ▷ (M)) ≫ completeSmoothMul K n h =
      (α_ (M) (M) (M)).hom ≫ ((M) ◁ completeSmoothMul K n h) ≫
        completeSmoothMul K n h := by
  apply completeSmoothTriple_hom_ext K n h
  intro b c d
  have he : ((completeIdentityChart K n h 0 b ⊗ₘ completeIdentityChart K n h 0 c) ⊗ₘ
      completeIdentityChart K n h 0 d) =
      lift (lift (fst ((G).X ⊗ (G).X) (G).X ≫ fst _ _ ≫
        completeIdentityChart K n h 0 b)
        (fst ((G).X ⊗ (G).X) (G).X ≫ snd _ _ ≫ completeIdentityChart K n h 0 c))
        (snd ((G).X ⊗ (G).X) (G).X ≫ completeIdentityChart K n h 0 d) := by
    simp only [← lift_fst_comp_snd_comp, comp_lift]
  rw [he, lift_whiskerRight_assoc, lift_lift_associator_hom_assoc, lift_whiskerLeft_assoc]
  exact completeSmoothMul_associative_evaluation K n h b c d
    (fst _ _ ≫ fst _ _) (fst _ _ ≫ snd _ _) (snd _ _)

/-- The global unit law in the monoidal presentation. -/
theorem completeSmoothMul_one :
    completeSmoothOne K n h ▷ (M) ≫ completeSmoothMul K n h = (λ_ (M)).hom := by
  apply (cancel_epi (λ_ (M)).inv).mp
  have he : (λ_ (M)).inv = lift (toUnit (M)) (𝟙 (M)) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp only
      [leftUnitor_inv_fst, leftUnitor_inv_snd, lift_fst, lift_snd]
  rw [he, lift_whiskerRight_assoc, completeSmoothMul_left_unit, lift_leftUnitor_hom]

/-- The global right unit law in the monoidal presentation. -/
theorem completeSmoothMul_mul_one :
    (M) ◁ completeSmoothOne K n h ≫ completeSmoothMul K n h = (ρ_ (M)).hom := by
  apply (cancel_epi (ρ_ (M)).inv).mp
  have he : (ρ_ (M)).inv = lift (𝟙 (M)) (toUnit (M)) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp only
      [rightUnitor_inv_fst, rightUnitor_inv_snd, lift_fst, lift_snd]
  rw [he, lift_whiskerLeft_assoc, completeSmoothMul_right_unit, lift_rightUnitor_hom]

/-- The constructed group object on the whole original smooth scheme. -/
@[instance_reducible] def completeSmoothGrpObj : GrpObj (M) where
  one := completeSmoothOne K n h
  mul := completeSmoothMul K n h
  one_mul := completeSmoothMul_one K n h
  mul_one := completeSmoothMul_mul_one K n h
  mul_assoc := completeSmoothMul_assoc K n h
  inv := completeSmoothInv K n h
  left_inv := completeSmoothMul_left_inv K n h
  right_inv := completeSmoothMul_right_inv K n h

attribute [local instance] completeSmoothGrpObj

/-- The constructed global smooth group is commutative. -/
instance completeSmooth_isCommMonObj : IsCommMonObj (M) where
  mul_comm := completeSmoothMul_comm K n h

/-- The entire original smooth polygon as a constructed commutative group over its original base. -/
def completeOriginalSmoothCommGroup : CommGrp (Over (Spec (.of (PowerSeries K)))) where
  X := (M)

end FLT.Mazur.PolygonInfinitesimalStages
