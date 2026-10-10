/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticSubgroupGenericDensity
public import FLT.Mazur.WeierstrassProjectivePointNegation
public import FLT.Mazur.WeierstrassGlobalNegationInvolution

/-!
# The actual finite subgroup closure is preserved by negation

Negation preserves the prescribed generic subgroup. Schematic density of
those actual points descends the ambient negation through the closed immersion.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits

namespace FLT.Mazur.EllipticSubgroupChart

open WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {K : Type*} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)
  (H : AddSubgroup (W.map (algebraMap A K)).toProjective.Point)

/-- Negating the actual generic points still gives points of the prescribed closure. -/
def closureGenericNegation : (∐ fun _ : H => Spec (.of K)) ⟶ gluedClosure A W H 1 2 :=
  Sigma.desc (fun P => closureGenericPoint A W H (-P))

/-- Generic negation agrees with the original global negation of the cubic. -/
theorem closureGenericNegation_toCurve :
    closureGenericPointsMap A W H ≫ closureToCurve A W H 1 2 ≫ integralCurveNegation W =
      closureGenericNegation A W H ≫ closureToCurve A W H 1 2 := by
  apply Sigma.hom_ext
  intro P
  rw [closureGenericPointsMap_point_assoc, closureGenericPoint_toCurve_assoc,
    ← Category.assoc, closureGenericNegation, Sigma.ι_comp_desc, closureGenericPoint_toCurve]
  exact (projectiveToIntegral_neg W P.1).symm

variable [Finite H]

/-- All closure equations vanish after restricting ambient negation to the actual closure. -/
theorem closureNegation_preserves_ideal : (closureToCurve A W H 1 2).ker ≤
    (closureToCurve A W H 1 2 ≫ integralCurveNegation W).ker := by
  have he : (closureGenericPointsMap A W H ≫ closureToCurve A W H 1 2 ≫
      integralCurveNegation W).ker =
      (closureToCurve A W H 1 2 ≫ integralCurveNegation W).ker := by
    rw [Scheme.Hom.ker_comp, (closureGenericPointsMap A W H).ker_eq_bot,
      Scheme.IdealSheafData.map_bot]
  rw [← he, closureGenericNegation_toCurve]
  exact Scheme.Hom.le_ker_comp _ _

/-- The original cubic negation restricted to the constructed finite subgroup closure. -/
def closureNegation : gluedClosure A W H 1 2 ⟶ gluedClosure A W H 1 2 :=
  closureToCurveLift A W H (closureToCurve A W H 1 2 ≫ integralCurveNegation W)
    (closureNegation_preserves_ideal A W H)

/-- The restriction is precisely the actual ambient negation. -/
@[reassoc] theorem closureNegation_toCurve :
    closureNegation A W H ≫ closureToCurve A W H 1 2 =
      closureToCurve A W H 1 2 ≫ integralCurveNegation W :=
  closureToCurveLift_inclusion A W H _ _

/-- Negation on the closure remains over the original valuation ring. -/
@[reassoc] theorem closureNegation_toBase :
    closureNegation A W H ≫ closureToBase A W H 1 2 = closureToBase A W H 1 2 := by
  rw [← closureToCurve_structure A W H 1 2, closureNegation_toCurve_assoc,
     integralCurveNegation_structure]

/-- The descended negation is involutive, as an equality of actual scheme morphisms. -/
@[reassoc] theorem closureNegation_comp :
    closureNegation A W H ≫ closureNegation A W H = 𝟙 _ := by
  apply closureToCurve_hom_ext A W H
  simp only [Category.assoc, closureNegation_toCurve, closureNegation_toCurve_assoc,
    integralCurveNegation_comp, Category.comp_id, Category.id_comp]

/-- The finite subgroup closure has the original negation as an actual automorphism. -/
def closureNegationIso : gluedClosure A W H 1 2 ≅ gluedClosure A W H 1 2 where
  hom := closureNegation A W H
  inv := closureNegation A W H
  hom_inv_id := closureNegation_comp A W H
  inv_hom_id := closureNegation_comp A W H

end FLT.Mazur.EllipticSubgroupChart
