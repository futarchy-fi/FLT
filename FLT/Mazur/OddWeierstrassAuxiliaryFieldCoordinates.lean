/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassAuxiliaryAffineSections
public import FLT.Mazur.OddWeierstrassAffineMarking

/-!
# Field coordinates of the original affine auxiliary sections

The chart coordinates are recovered from actual scheme morphisms. Their
comparison with the faithful affine marking detects distinct coordinates of
the first two basis labels and of the first label and its inverse.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry WeierstrassCurve

namespace FLT.Mazur.OddWeierstrassParameter

open IntegralWeierstrassParameter (OddChartRing oddChartEquation oddChart_discriminant)
open UniversalWeierstrass (Labels)

open WeierstrassIntegralChart

variable (K : Type) [Field K] [Algebra OddChartRing K]
  (f : fieldTest K ⟶ levelThree) (a : Labels 3) (ha : a ≠ 1)

/-- Coordinates of the original affine marked section over a coefficient field. -/
def auxiliaryFieldChart : Coordinate oddChartEquation 2 →ₐ[OddChartRing] K :=
  fieldChartAlgHom oddChartEquation 2 (f.left ≫ auxiliaryAffineSection a ha) (by
    rw [Category.assoc, auxiliaryAffineSection_base]
    exact f.w)

/-- The recovered chart algebra map is the original affine section on the test field. -/
theorem auxiliaryFieldChart_spec :
    Spec.map (CommRingCat.ofHom (auxiliaryFieldChart K f a ha).toRingHom) =
      f.left ≫ auxiliaryAffineSection a ha := fieldChartAlgHom_spec ..

/-- The recovered coordinates satisfy the original nonsingular affine equation. -/
theorem auxiliaryFieldChart_nonsingular :
    (oddChartEquation.map (algebraMap OddChartRing K)).toAffine.Nonsingular
      (auxiliaryFieldChart K f a ha (coord oddChartEquation 2 0))
      (auxiliaryFieldChart K f a ha (coord oddChartEquation 2 1)) := by
  let _ : oddChartEquation.IsElliptic := ⟨oddChart_discriminant⟩
  apply Affine.equation_iff_nonsingular.mp
  apply (Projective.equation_some _ _).mp
  have he := chartAlgHom_equation oddChartEquation 2 (auxiliaryFieldChart K f a ha)
  convert he using 1
  funext i
  fin_cases i <;> simp

variable [DecidableEq K]

/-- The original marking has exactly the coordinates recovered from its affine chart lift. -/
theorem auxiliaryAffineMarking_coordinates :
    auxiliaryAffineMarking K f a.toAdd =
      .some (auxiliaryFieldChart K f a ha (coord oddChartEquation 2 0))
        (auxiliaryFieldChart K f a ha (coord oddChartEquation 2 1))
        (auxiliaryFieldChart_nonsingular K f a ha) := by
  apply (integralAffinePointAddEquiv oddChartEquation oddChart_discriminant).injective
  simp only [auxiliaryAffineMarking, AddMonoidHom.comp_apply,
    AddEquiv.toAddMonoidHom_eq_coe, AddMonoidHom.coe_ofClass, AddEquiv.apply_symm_apply]
  apply Additive.toMul.injective
  apply Over.OverMorphism.ext
  change (AuxiliaryLevel.markingOf universalGroup (Labels 3)
    (f ≫ levelThreeInclusion) a).left = _
  rw [AuxiliaryLevel.markingOf_comp]
  change f.left ≫ (levelThreeMarking a).left = _
  rw [← auxiliaryAffineSection_inclusion a ha, ← Category.assoc,
    ← auxiliaryFieldChart_spec K f a ha]
  exact (projectiveToIntegral_affineAlgHom oddChartEquation (auxiliaryFieldChart K f a ha)
    (auxiliaryFieldChart_nonsingular K f a ha)).symm

omit [DecidableEq K] in
/-- Different nonopposite labels have different actual affine abscissas. -/
theorem auxiliaryFieldChart_x_ne (b : Labels 3) (hb : b ≠ 1)
    (hab : a ≠ b) (hab' : a ≠ b⁻¹) :
    auxiliaryFieldChart K f a ha (coord oddChartEquation 2 0) ≠
      auxiliaryFieldChart K f b hb (coord oddChartEquation 2 0) := by
  classical
  intro hx
  have hi := auxiliaryAffineMarking_injective K f
  have hp := auxiliaryAffineMarking_coordinates K f a ha
  have hq := auxiliaryAffineMarking_coordinates K f b hb
  rcases (Affine.Point.X_eq_iff (h₁ := auxiliaryFieldChart_nonsingular K f a ha)
    (h₂ := auxiliaryFieldChart_nonsingular K f b hb)).mp hx with he | he
  · exact hab (congrArg Multiplicative.ofAdd (hi (hp.trans (he.trans hq.symm))))
  · have he' := hp.trans (he.trans (congrArg Neg.neg hq).symm)
    exact hab' (congrArg Multiplicative.ofAdd
      (hi (he'.trans ((auxiliaryAffineMarking K f).map_neg b.toAdd).symm)))

omit [DecidableEq K] in
/-- An order-three label has ordinate different from its inverse's ordinate. -/
theorem auxiliaryFieldChart_y_ne_neg (han : a ≠ a⁻¹) :
    auxiliaryFieldChart K f a ha (coord oddChartEquation 2 1) ≠
      (oddChartEquation.map (algebraMap OddChartRing K)).toAffine.negY
        (auxiliaryFieldChart K f a ha (coord oddChartEquation 2 0))
        (auxiliaryFieldChart K f a ha (coord oddChartEquation 2 1)) := by
  classical
  intro hy
  have hp := auxiliaryAffineMarking_coordinates K f a ha
  have he : auxiliaryAffineMarking K f a.toAdd = -auxiliaryAffineMarking K f a.toAdd := by
    rw [hp, Affine.Point.neg_some, Affine.Point.some.injEq]
    exact ⟨rfl, hy⟩
  exact han (congrArg Multiplicative.ofAdd (auxiliaryAffineMarking_injective K f
    (he.trans ((auxiliaryAffineMarking K f).map_neg a.toAdd).symm)))

end FLT.Mazur.OddWeierstrassParameter
