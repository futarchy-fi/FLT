/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluAffineSectionChart
public import FLT.FreyCurve.Serre.VeluKernelRationalEvaluation
public import FLT.FreyCurve.Serre.VeluKernelBaseChangeScheme

/-!
# Original kernel sections commute with rational descent

Every original geometric component has exactly the rational kernel morphism as
its coefficient projection. The comparison uses the original x and y coordinates.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry

namespace WeierstrassCurve.Velu

open FLT.Mazur FLT.Mazur.WeierstrassIntegralChart

variable (E : WeierstrassCurve ℚ) [E.IsElliptic] (p : ℕ) [Fact p.Prime]
  (q : (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p →ₗ[ZMod p] ZMod p)
  (hq : Function.Surjective q)
  (hfixed : ∀ g t, q (E.torsionGaloisRepresentation p g t) = q t)

/-- Each original section projects to the actual rational kernel evaluation. -/
@[reassoc] theorem primeKernelRationalMap_section (i : ZMod p) :
    ((affineRationalGroupSectionAddHom (E.map (algebraMap ℚ (AlgebraicClosure ℚ)))
      (primeKernelParam E p q hq i)).toMul).left ≫ integralCoefficientMorphism E =
        Spec.map (CommRingCat.ofHom
          (primeKernelDescentEvaluation E p q hq hfixed i).toRingHom) ≫
            primeKernelRationalMap E p q hq hfixed := by
  by_cases hi : i = 0
  · subst i
    rw [map_zero, affineRationalGroupSection_zero, integralCoefficientMorphism_zero,
      primeKernelRationalMap_evaluation_zero]
  · rw [primeKernelRationalMap_evaluation_ne_zero E p q hq hfixed i hi]
    have hP : primeKernelParam E p q hq i ≠ 0 := by
      intro h
      apply hi
      exact (primeKernelParam_injective E p q hq) (h.trans (map_zero _).symm)
    generalize he : primeKernelParam E p q hq i = P at hP ⊢
    cases P with
    | zero => exact (hP rfl).elim
    | some x y h =>
      rw [affineRationalGroupSection_some, Category.assoc,
        integralCurveChart_coefficientMorphism, ← Category.assoc]
      congr 1
      change Spec.map _ ≫ Spec.map _ = Spec.map _
      rw [← Spec.map_comp]
      apply congrArg (fun f ↦ Spec.map (CommRingCat.ofHom f))
      change (((evaluation (E.map (algebraMap ℚ (AlgebraicClosure ℚ))) 2 ![x, y, 1]
        ((WeierstrassCurve.Projective.equation_some x y).mpr h.left) rfl).restrictScalars ℚ).comp
          (chartCoefficientMap E 2)).toRingHom = _
      apply congrArg AlgHom.toRingHom
      apply hom_ext
      intro j
      simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply,
        chartCoefficientMap_coord, evaluation_coord]
      fin_cases j
      · change x = primeKernelAffineEvaluation E p q hq hfixed i hi
          (primeKernelAffineChart E p q hq hfixed (coord E 2 0))
        rw [primeKernelAffineChart_x, primeKernelAffineEvaluation_x, he]
        rfl
      · change y = primeKernelAffineEvaluation E p q hq hfixed i hi
          (primeKernelAffineChart E p q hq hfixed (coord E 2 1))
        rw [primeKernelAffineChart_y, primeKernelAffineEvaluation_y, he]
        rfl
      · change 1 = primeKernelAffineEvaluation E p q hq hfixed i hi
          (primeKernelAffineChart E p q hq hfixed (coord E 2 2))
        rw [coord_self, map_one, map_one]

end WeierstrassCurve.Velu
