/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonAdicCoefficientStages
public import FLT.Mazur.OneGonAdicSmoothProjection
public import FLT.Mazur.WeierstrassSmoothCoefficientComposition

/-!
# Smooth coefficient squares at the original adic orders

The finite smooth comparisons preserve the actual quotient parameter and
commute with both adjacent restriction and projection to the complete base.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.OneGonAdicCharacterTower
open OneGonSmoothing WeierstrassIntegralChart AdicFormallySmoothStages
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R S : Type} [CommRing R] [CommRing S]
  (I : Ideal R) (J : Ideal S) (f : R →+* S) (hf : I ≤ J.comap f) (t : R)

/-- The actual adic coefficient map retains the full cubic equation. -/
theorem stageCoefficient_equation (m : ℕ) :
    equation (parameter J (f t) m) =
      (equation (parameter I t m)).map (stageCoefficient I J f hf m) := by
  rw [equation_map, stageCoefficient_parameter]

/-- Coefficient projection between the actual finite smooth schemes. -/
def stageSmoothCoefficient (m : ℕ) :
    (stageGroup J (f t) m).X.left ⟶ (stageGroup I t m).X.left :=
  smoothCoefficientMapTo _ _ (stageCoefficient I J f hf m)
    (stageCoefficient_equation I J f hf t m)

/-- The original adjacent map agrees with the named-equation coefficient map. -/
theorem smoothRestriction_coefficientMapTo (m : ℕ) :
    smoothRestriction I t m =
      smoothCoefficientMapTo _ _ (restriction I m).toRingHom
        (restriction_equation I t m).symm := by
  let _ := (restriction I m).toRingHom.toAlgebra
  unfold smoothRestriction smoothCoefficientMapTo
  rw [← equationGroupTransport_inv_left (restriction_equation I t m)]
  rfl

/-- The original complete-base projection agrees with the named coefficient map. -/
theorem smoothProjection_coefficientMapTo (m : ℕ) :
    smoothProjection I t m =
      smoothCoefficientMapTo (equation t) _ (Ideal.Quotient.mk (I ^ (m + 1)))
        (equation_map t (Ideal.Quotient.mk (I ^ (m + 1)))).symm := by
  unfold smoothProjection smoothCoefficientMapTo
  rw [← equationGroupTransport_inv_left
    (equation_map t (algebraMap R (StageRing I m)))]
  rfl

/-- Adjacent smooth restriction retains the original quotient-base morphism. -/
@[reassoc] theorem smoothRestriction_structure (m : ℕ) :
    smoothRestriction I t m ≫ (stageGroup I t (m + 1)).X.hom =
      (stageGroup I t m).X.hom ≫ Spec.map (CommRingCat.ofHom (restriction I m).toRingHom) := by
  rw [smoothRestriction_coefficientMapTo]
  exact smoothCoefficientMapTo_structure _ _ _ _

/-- The finite smooth projection retains its original complete coefficient base. -/
@[reassoc] theorem smoothProjection_structure (m : ℕ) :
    smoothProjection I t m ≫ integralSmoothStructure (equation t) =
      (stageGroup I t m).X.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk _)) := by
  rw [smoothProjection_coefficientMapTo]
  exact smoothCoefficientMapTo_structure _ _ _ _

/-- Full smooth coefficient change commutes with adjacent reduction. -/
@[reassoc] theorem stageSmoothCoefficient_restriction (m : ℕ) :
    smoothRestriction J (f t) m ≫ stageSmoothCoefficient I J f hf t (m + 1) =
      stageSmoothCoefficient I J f hf t m ≫ smoothRestriction I t m := by
  rw [smoothRestriction_coefficientMapTo, smoothRestriction_coefficientMapTo]
  unfold stageSmoothCoefficient
  rw [smoothCoefficientMapTo_comp _ _ _ _ _ _ _
    (by rw [equation_map]; rfl),
    smoothCoefficientMapTo_comp _ _ _ _ _ _ _
    (by rw [equation_map]; rfl)]
  exact smoothCoefficientMapTo_congr _ _ (stageCoefficient_restriction I J f hf m) _ _

/-- Finite smooth coefficient change retains the projection to the original complete curve. -/
@[reassoc] theorem stageSmoothCoefficient_projection (m : ℕ) :
    smoothProjection J (f t) m ≫
      smoothCoefficientMapTo (equation t) (equation (f t)) f (equation_map t f).symm =
        stageSmoothCoefficient I J f hf t m ≫ smoothProjection I t m := by
  rw [smoothProjection_coefficientMapTo, smoothProjection_coefficientMapTo]
  unfold stageSmoothCoefficient
  have hq : (stageCoefficient I J f hf m).comp (Ideal.Quotient.mk (I ^ (m + 1))) =
      (Ideal.Quotient.mk (J ^ (m + 1))).comp f := by
    ext r
    rfl
  have h₁ := smoothCoefficientMapTo_comp (equation t) (equation (f t))
    (equation (parameter J (f t) m)) f (Ideal.Quotient.mk (J ^ (m + 1)))
    (equation_map t f).symm (equation_map (f t) (Ideal.Quotient.mk _)).symm
    (by rw [equation_map]; rfl)
  have h₂ := smoothCoefficientMapTo_comp (equation t) (equation (parameter I t m))
    (equation (parameter J (f t) m)) (Ideal.Quotient.mk (I ^ (m + 1)))
    (stageCoefficient I J f hf m) (equation_map t (Ideal.Quotient.mk _)).symm
    (stageCoefficient_equation I J f hf t m) (by rw [equation_map]; rfl)
  exact h₁.trans (h₂.trans (smoothCoefficientMapTo_congr _ _ hq _ _)).symm

end FLT.Mazur.OneGonAdicCharacterTower
