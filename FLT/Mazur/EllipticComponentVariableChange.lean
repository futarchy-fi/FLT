/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticComponentQuotient
public import FLT.Mazur.EllipticVariableChangeReduction

/-!
# Component quotients under integral variable changes

The generic point-group isomorphism induced by an integral unit variable
change preserves the actual nonsingular-reduction subgroup E₀. It therefore
induces an additive equivalence of the rational component quotients E/E₀.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve

variable {K : Type*} [Field K] [DecidableEq K] (A : ValuationSubring K) (W : WeierstrassCurve A)
  (C : VariableChange A) [(W.map (algebraMap A K)).IsElliptic]

/-- The generic affine point-group equivalence for an integral variable change. -/
noncomputable def integralAffineVariableChange :
    ((C • W).map (algebraMap A K)).toAffine.Point ≃+
      (W.map (algebraMap A K)).toAffine.Point := by
  exact (Affine.Point.equivOfEq (map_variableChange (W := W) (C := C)
    (φ := algebraMap A K)).symm).trans
      (Affine.Point.equivVariableChange (W.map (algebraMap A K)) (C.map (algebraMap A K)))

/-- The affine point-group equivalence preserves smooth reduction. -/
theorem integralAffineVariableChange_smooth
    (P : ((C • W).map (algebraMap A K)).toAffine.Point) :
    SmoothReduction A W (integralAffineVariableChange A W C P).toProjective ↔
      SmoothReduction A (C • W) P.toProjective := by
  cases P with
  | zero =>
    rw [← Affine.Point.zero_def, map_zero]
    exact iff_of_true (smoothReduction_zero A W) (smoothReduction_zero A (C • W))
  | some x y h =>
    simp only [integralAffineVariableChange, AddEquiv.trans_apply,
      Affine.Point.equivOfEq_some, Affine.Point.equivVariableChange_some]
    exact smoothReduction_variableChange_affine A W C x y h _

/-- The generic projective point-group equivalence for an integral variable change. -/
noncomputable def integralProjectiveVariableChange :
    ((C • W).map (algebraMap A K)).toProjective.Point ≃+
      (W.map (algebraMap A K)).toProjective.Point := by
  exact ((Projective.Point.toAffineAddEquiv _).trans
    (integralAffineVariableChange A W C)).trans (Projective.Point.toAffineAddEquiv _).symm

/-- The projective point-group equivalence preserves E₀ membership. -/
theorem integralProjectiveVariableChange_smooth
    (P : ((C • W).map (algebraMap A K)).toProjective.Point) :
    SmoothReduction A W (integralProjectiveVariableChange A W C P) ↔
      SmoothReduction A (C • W) P := by
  obtain ⟨p, rfl⟩ := (Projective.Point.toAffineAddEquiv
    ((C • W).map (algebraMap A K)).toProjective).symm.surjective P
  simp only [integralProjectiveVariableChange, AddEquiv.trans_apply,
    AddEquiv.apply_symm_apply]
  simpa only [Projective.Point.toAffineAddEquiv_symm_apply]
    using integralAffineVariableChange_smooth A W C p

/-- Integral variable changes carry the actual nonsingular-reduction subgroup onto E₀. -/
theorem integralProjectiveVariableChange_map_E0 :
    (ellipticE0 A (C • W)).map (integralProjectiveVariableChange A W C).toAddMonoidHom =
      ellipticE0 A W := by
  ext P
  constructor
  · rintro ⟨Q, hQ, rfl⟩
    exact (integralProjectiveVariableChange_smooth A W C Q).mpr hQ
  · intro hP
    refine ⟨(integralProjectiveVariableChange A W C).symm P, ?_,
      (integralProjectiveVariableChange A W C).apply_symm_apply P⟩
    apply (integralProjectiveVariableChange_smooth A W C _).mp
    simpa only [AddEquiv.apply_symm_apply] using (show SmoothReduction A W P from hP)

/-- Integral unit variable changes induce additive equivalences of rational component quotients. -/
noncomputable def integralComponentVariableChange :
    EllipticComponentQuotient A (C • W) ≃+ EllipticComponentQuotient A W :=
  QuotientAddGroup.congr _ _ (integralProjectiveVariableChange A W C)
    (integralProjectiveVariableChange_map_E0 A W C)

/-- The quotient equivalence sends the class of a point to the class of its coordinate transform. -/
theorem integralComponentVariableChange_mk
    (P : ((C • W).map (algebraMap A K)).toProjective.Point) :
    integralComponentVariableChange A W C (ellipticComponentHom A (C • W) P) =
      ellipticComponentHom A W (integralProjectiveVariableChange A W C P) := rfl

end FLT.Mazur
