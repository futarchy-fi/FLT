/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicQuadraticDescent

/-! # Comparison of reciprocal square-root covers

The covers adjoining roots of a unit and its inverse are isomorphic over
the coefficient base. Both algebra maps send the distinguished root to the
inverse root and commute with the sign involution. This supplies the
coefficient-cover comparison for reciprocal Legendre transport; comparison
of the cyclic maps after this base change remains to be established.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Polynomial
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R] (d : Rˣ) [Fact (IsUnit (2 : R))]

/-- Scaling the inverse-parameter root solves the original etale presentation. -/
theorem quadraticReciprocal_hasMap :
    (quadraticEtalePair d).HasMap
      (algebraMap R (QuadraticEtaleRing d⁻¹) (d : R) *
        (quadraticEtaleUnit d⁻¹ : QuadraticEtaleRing d⁻¹)) := by
  constructor
  · change aeval _ (X ^ 2 - C (d : R)) = 0
    simp only [map_sub, map_pow, aeval_X, aeval_C, mul_pow, quadraticEtaleUnit_square]
    rw [← map_pow, ← map_mul]
    simp [pow_two, mul_assoc]
  · change IsUnit (aeval _ (quadraticRootPolynomial d).derivative)
    have hd : (quadraticRootPolynomial d).derivative = 2 * X := by
      simp [quadraticRootPolynomial]
      ring
    rw [hd, map_mul, map_ofNat, aeval_X]
    exact ((Fact.out : IsUnit (2 : R)).map (algebraMap R _)).mul
      ((d.isUnit.map (algebraMap R _)).mul (quadraticEtaleUnit d⁻¹).isUnit)

/-- The map from the root algebra of d to the root algebra of its inverse. -/
def quadraticReciprocalHom : QuadraticEtaleRing d →ₐ[R] QuadraticEtaleRing d⁻¹ :=
  (quadraticEtalePair d).lift _ (quadraticReciprocal_hasMap d)

/-- The comparison map scales the target root by d. -/
theorem quadraticReciprocalHom_root :
    quadraticReciprocalHom d (quadraticEtalePair d).X =
      algebraMap R _ (d : R) * (quadraticEtaleUnit d⁻¹ : QuadraticEtaleRing d⁻¹) :=
  StandardEtalePair.lift_X _ _ _

/-- The comparison formula on the distinguished root unit. -/
theorem quadraticReciprocalHom_unit :
    quadraticReciprocalHom d (quadraticEtaleUnit d : QuadraticEtaleRing d) =
      algebraMap R _ (d : R) * (quadraticEtaleUnit d⁻¹ : QuadraticEtaleRing d⁻¹) := by
  simpa only [quadraticEtaleUnit, IsUnit.unit_spec] using quadraticReciprocalHom_root d

/-- The comparison intertwines the two sign involutions. -/
theorem quadraticReciprocalHom_sign :
    (quadraticReciprocalHom d).comp (quadraticEtaleNeg d) =
      (quadraticEtaleNeg d⁻¹).comp (quadraticReciprocalHom d) := by
  apply (quadraticEtalePair d).hom_ext
  simp [AlgHom.comp_apply, quadraticEtaleNeg_root, quadraticReciprocalHom_root,
    quadraticEtaleNeg_unit]

/-- The inverse comparison map, with target specified without type transport. -/
def quadraticReciprocalInvHom : QuadraticEtaleRing d⁻¹ →ₐ[R] QuadraticEtaleRing d :=
  (quadraticEtalePair d⁻¹).lift
    (algebraMap R _ ((d⁻¹ : Rˣ) : R) * (quadraticEtaleUnit d : QuadraticEtaleRing d))
    (by
      constructor
      · change aeval _ (X ^ 2 - C ((d⁻¹ : Rˣ) : R)) = 0
        simp only [map_sub, map_pow, aeval_X, aeval_C, mul_pow, quadraticEtaleUnit_square]
        rw [← map_pow, ← map_mul]
        simp [pow_two, mul_assoc]
      · change IsUnit (aeval _ (quadraticRootPolynomial d⁻¹).derivative)
        have hd : (quadraticRootPolynomial d⁻¹).derivative = 2 * X := by
          simp [quadraticRootPolynomial]
          ring
        rw [hd, map_mul, map_ofNat, aeval_X]
        exact ((Fact.out : IsUnit (2 : R)).map (algebraMap R _)).mul
          (((d⁻¹).isUnit.map (algebraMap R _)).mul (quadraticEtaleUnit d).isUnit))

/-- The return map scales the target root by the inverse parameter. -/
theorem quadraticReciprocalInvHom_root :
    quadraticReciprocalInvHom d (quadraticEtalePair d⁻¹).X =
      algebraMap R _ ((d⁻¹ : Rˣ) : R) * (quadraticEtaleUnit d : QuadraticEtaleRing d) :=
  StandardEtalePair.lift_X _ _ _

/-- The return comparison formula on the distinguished root unit. -/
theorem quadraticReciprocalInvHom_unit :
    quadraticReciprocalInvHom d (quadraticEtaleUnit d⁻¹ : QuadraticEtaleRing d⁻¹) =
      algebraMap R _ ((d⁻¹ : Rˣ) : R) * (quadraticEtaleUnit d : QuadraticEtaleRing d) := by
  simpa only [quadraticEtaleUnit, IsUnit.unit_spec] using quadraticReciprocalInvHom_root d

/-- The return map composed with the comparison is the identity. -/
theorem quadraticReciprocalInvHom_comp :
    (quadraticReciprocalInvHom d).comp (quadraticReciprocalHom d) = AlgHom.id R _ := by
  apply (quadraticEtalePair d).hom_ext
  simp only [AlgHom.comp_apply, AlgHom.id_apply, quadraticReciprocalHom_root, map_mul,
    AlgHom.commutes, quadraticReciprocalInvHom_unit]
  rw [← mul_assoc, ← map_mul]
  simp [quadraticEtaleUnit, IsUnit.unit_spec]

/-- The comparison composed with the return map is the identity. -/
theorem quadraticReciprocalHom_comp :
    (quadraticReciprocalHom d).comp (quadraticReciprocalInvHom d) = AlgHom.id R _ := by
  apply (quadraticEtalePair d⁻¹).hom_ext
  simp only [AlgHom.comp_apply, AlgHom.id_apply, quadraticReciprocalInvHom_root, map_mul,
    AlgHom.commutes, quadraticReciprocalHom_unit]
  rw [← mul_assoc, ← map_mul]
  simp [quadraticEtaleUnit, IsUnit.unit_spec]

/-- The reciprocal square-root algebras are isomorphic over the base. -/
def quadraticReciprocalEquiv : QuadraticEtaleRing d ≃ₐ[R] QuadraticEtaleRing d⁻¹ :=
  AlgEquiv.ofAlgHom (quadraticReciprocalHom d) (quadraticReciprocalInvHom d)
    (quadraticReciprocalHom_comp d) (quadraticReciprocalInvHom_comp d)

/-- The image of the original root times the target root is one. -/
theorem quadraticReciprocalHom_unit_mul :
    quadraticReciprocalHom d (quadraticEtaleUnit d : QuadraticEtaleRing d) *
      (quadraticEtaleUnit d⁻¹ : QuadraticEtaleRing d⁻¹) = 1 := by
  rw [quadraticReciprocalHom_unit, mul_assoc, ← pow_two,
    quadraticEtaleUnit_square, ← map_mul]
  simp

/-- The comparison sends the root unit to the inverse target root unit. -/
theorem quadraticReciprocalHom_unit_map :
    Units.map (quadraticReciprocalHom d).toMonoidHom (quadraticEtaleUnit d) =
      (quadraticEtaleUnit d⁻¹)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  apply Units.ext
  exact quadraticReciprocalHom_unit_mul d

/-- The reciprocal root covers are isomorphic as schemes. -/
def quadraticReciprocalCoverIso :
    Spec (.of (QuadraticEtaleRing d⁻¹)) ≅ Spec (.of (QuadraticEtaleRing d)) :=
  Scheme.Spec.mapIso (quadraticReciprocalEquiv d).toRingEquiv.toCommRingCatIso.op

/-- The cover isomorphism preserves the coefficient base. -/
theorem quadraticReciprocalCoverIso_over :
    (quadraticReciprocalCoverIso d).hom ≫ quadraticEtaleCover d =
      quadraticEtaleCover d⁻¹ := by
  change Spec.map (CommRingCat.ofHom (quadraticReciprocalHom d).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap R (QuadraticEtaleRing d))) =
      Spec.map (CommRingCat.ofHom (algebraMap R (QuadraticEtaleRing d⁻¹)))
  rw [← Spec.map_comp]
  congr 1
  ext x
  exact (quadraticReciprocalHom d).commutes x

omit [Fact (IsUnit (2 : R))] in
private theorem reciprocal_spec_comp {A B C : Type u}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra R C] (f : B →ₐ[R] C) (g : A →ₐ[R] B) :
    Spec.map (CommRingCat.ofHom (f.comp g).toRingHom) =
      Spec.map (CommRingCat.ofHom f.toRingHom) ≫ Spec.map (CommRingCat.ofHom g.toRingHom) :=
  Spec.map_comp (CommRingCat.ofHom g.toRingHom) (CommRingCat.ofHom f.toRingHom)

/-- The cover isomorphism commutes with the sign involutions. -/
theorem quadraticReciprocalCoverIso_sign :
    quadraticEtaleSignMorphism d⁻¹ ≫ (quadraticReciprocalCoverIso d).hom =
      (quadraticReciprocalCoverIso d).hom ≫ quadraticEtaleSignMorphism d := by
  have h := congrArg (fun f : QuadraticEtaleRing d →ₐ[R] QuadraticEtaleRing d⁻¹ =>
    Spec.map (CommRingCat.ofHom f.toRingHom)) (quadraticReciprocalHom_sign d)
  rw [reciprocal_spec_comp, reciprocal_spec_comp] at h
  exact h.symm

/-- The return comparison also sends the root to the inverse root. -/
theorem quadraticReciprocalInvHom_unit_map :
    Units.map (quadraticReciprocalInvHom d).toMonoidHom (quadraticEtaleUnit d⁻¹) =
      (quadraticEtaleUnit d)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  apply Units.ext
  change quadraticReciprocalInvHom d (quadraticEtaleUnit d⁻¹ : QuadraticEtaleRing d⁻¹) *
    (quadraticEtaleUnit d : QuadraticEtaleRing d) = 1
  rw [quadraticReciprocalInvHom_unit, mul_assoc, ← pow_two,
    quadraticEtaleUnit_square, ← map_mul]
  simp

/-- The reciprocal root algebra is a domain if the original one is. -/
theorem quadraticReciprocal_isDomain [IsDomain (QuadraticEtaleRing d)] :
    IsDomain (QuadraticEtaleRing d⁻¹) :=
  (quadraticReciprocalEquiv d).symm.toMulEquiv.isDomain (QuadraticEtaleRing d)

/-- Noetherianity transfers to the reciprocal root algebra. -/
theorem quadraticReciprocal_isNoetherian [IsNoetherianRing (QuadraticEtaleRing d)] :
    IsNoetherianRing (QuadraticEtaleRing d⁻¹) :=
  isNoetherianRing_of_ringEquiv (QuadraticEtaleRing d) (quadraticReciprocalEquiv d).toRingEquiv

end WeierstrassCurve.CubicCharts
