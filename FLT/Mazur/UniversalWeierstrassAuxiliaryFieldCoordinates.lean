/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassAuxiliaryAffineSections
public import FLT.Mazur.UniversalWeierstrassMarkedCoordinateRigidity

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

namespace FLT.Mazur.UniversalWeierstrass

open WeierstrassIntegralChart

variable (K : Type) [Field K] [Algebra ParameterRing K]
  (f : fieldTest K ⟶ levelFour) (a : Labels 4) (ha : a ≠ 1)

/-- Coordinates of the original affine marked section over a coefficient field. -/
def auxiliaryFieldChart : Coordinate smoothEquation 2 →ₐ[ParameterRing] K :=
  fieldChartAlgHom smoothEquation 2 (f.left ≫ auxiliaryAffineSection a ha) (by
    rw [Category.assoc, auxiliaryAffineSection_base]
    exact f.w)

/-- The recovered chart algebra map is the original affine section on the test field. -/
theorem auxiliaryFieldChart_spec :
    Spec.map (CommRingCat.ofHom (auxiliaryFieldChart K f a ha).toRingHom) =
      f.left ≫ auxiliaryAffineSection a ha := fieldChartAlgHom_spec ..

/-- The recovered coordinates satisfy the original nonsingular affine equation. -/
theorem auxiliaryFieldChart_nonsingular :
    (smoothEquation.map (algebraMap ParameterRing K)).toAffine.Nonsingular
      (auxiliaryFieldChart K f a ha (coord smoothEquation 2 0))
      (auxiliaryFieldChart K f a ha (coord smoothEquation 2 1)) := by
  let _ : smoothEquation.IsElliptic := ⟨smoothEquation_discriminant⟩
  apply Affine.equation_iff_nonsingular.mp
  apply (Projective.equation_some _ _).mp
  have he := chartAlgHom_equation smoothEquation 2 (auxiliaryFieldChart K f a ha)
  convert he using 1
  funext i
  fin_cases i <;> simp

variable [DecidableEq K]

/-- The original marking has exactly the coordinates recovered from its affine chart lift. -/
theorem auxiliaryAffineMarking_coordinates :
    auxiliaryAffineMarking K f a.toAdd =
      .some (auxiliaryFieldChart K f a ha (coord smoothEquation 2 0))
        (auxiliaryFieldChart K f a ha (coord smoothEquation 2 1))
        (auxiliaryFieldChart_nonsingular K f a ha) := by
  apply (integralAffinePointAddEquiv smoothEquation smoothEquation_discriminant).injective
  simp only [auxiliaryAffineMarking, AddMonoidHom.comp_apply,
    AddEquiv.toAddMonoidHom_eq_coe, AddMonoidHom.coe_ofClass, AddEquiv.apply_symm_apply]
  apply Additive.toMul.injective
  apply Over.OverMorphism.ext
  change (AuxiliaryLevel.markingOf universalGroup (Labels 4)
    (f ≫ auxiliaryInclusion 4) a).left = _
  rw [AuxiliaryLevel.markingOf_comp]
  change f.left ≫ (auxiliaryMarking 4 a).left = _
  rw [← auxiliaryAffineSection_inclusion a ha, ← Category.assoc,
    ← auxiliaryFieldChart_spec K f a ha]
  exact (projectiveToIntegral_affineAlgHom smoothEquation (auxiliaryFieldChart K f a ha)
    (auxiliaryFieldChart_nonsingular K f a ha)).symm

omit [DecidableEq K] in
/-- Different nonopposite labels have different actual affine abscissas. -/
theorem auxiliaryFieldChart_x_ne (b : Labels 4) (hb : b ≠ 1)
    (hab : a ≠ b) (hab' : a ≠ b⁻¹) :
    auxiliaryFieldChart K f a ha (coord smoothEquation 2 0) ≠
      auxiliaryFieldChart K f b hb (coord smoothEquation 2 0) := by
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
/-- An order-four label has ordinate different from its inverse's ordinate. -/
theorem auxiliaryFieldChart_y_ne_neg (han : a ≠ a⁻¹) :
    auxiliaryFieldChart K f a ha (coord smoothEquation 2 1) ≠
      (smoothEquation.map (algebraMap ParameterRing K)).toAffine.negY
        (auxiliaryFieldChart K f a ha (coord smoothEquation 2 0))
        (auxiliaryFieldChart K f a ha (coord smoothEquation 2 1)) := by
  classical
  intro hy
  have hp := auxiliaryAffineMarking_coordinates K f a ha
  have he : auxiliaryAffineMarking K f a.toAdd = -auxiliaryAffineMarking K f a.toAdd := by
    rw [hp, Affine.Point.neg_some, Affine.Point.some.injEq]
    exact ⟨rfl, hy⟩
  exact han (congrArg Multiplicative.ofAdd (auxiliaryAffineMarking_injective K f
    (he.trans ((auxiliaryAffineMarking K f).map_neg a.toAdd).symm)))

end FLT.Mazur.UniversalWeierstrass
