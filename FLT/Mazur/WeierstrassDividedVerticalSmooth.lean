/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDilatationCoefficients
public import FLT.Mazur.PrincipalAffineRefinement
public import Mathlib.RingTheory.Etale.StandardEtale
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# The vertical derivative open of the divided chart is relatively smooth

The monic divided equation is etale over the abscissa line after inverting
its vertical derivative. This proves smoothness over the original coefficient
ring, including points whose original cubic contraction is singular.
-/

@[expose] public noncomputable section
open Polynomial AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDilatation
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)

/-- The actual vertical derivative in the divided coordinate algebra. -/
def verticalDerivative : Coordinate W s b3 b4 b6 :=
  AdjoinRoot.mk (polynomial W s b3 b4 b6) (polynomial W s b3 b4 b6).derivative

/-- Its explicit value retains the original divided coefficients. -/
theorem verticalDerivative_eq :
    verticalDerivative W s b3 b4 b6 = 2 * y W s b3 b4 b6 +
      algebraMap R _ W.a₁ * x W s b3 b4 b6 + algebraMap R _ b3 := by
  have hd : (polynomial W s b3 b4 b6).derivative =
      2 * X + C (C W.a₁ * X + C b3) := by
    simp only [polynomial, derivative_sub, derivative_add, derivative_X_pow,
      derivative_C_mul_X, derivative_C, sub_zero]
    norm_num [map_ofNat]
  rw [verticalDerivative, hd, map_add, map_mul]
  change 2 * y W s b3 b4 b6 +
    algebraMap R[X] _ (C W.a₁ * X + C b3) = _
  simp only [map_add, map_mul]
  exact (add_assoc _ _ _).symm

/-- The divided equation and its derivative form a concrete standard etale pair. -/
def verticalEtalePair : StandardEtalePair R[X] where
  f := polynomial W s b3 b4 b6
  monic_f := polynomial_monic W s b3 b4 b6
  g := (polynomial W s b3 b4 b6).derivative
  cond := ⟨1, 0, 1, by simp⟩

/-- The actual derivative localization is smooth over the original coefficient ring. -/
theorem verticalLocalization_smooth :
    Algebra.Smooth R (Localization.Away (verticalDerivative W s b3 b4 b6)) := by
  let _ : Algebra.Smooth R R[X] := ⟨inferInstance, inferInstance⟩
  let _ : Algebra.Smooth R[X] (Localization.Away (verticalDerivative W s b3 b4 b6)) :=
    Algebra.Smooth.of_equiv (verticalEtalePair W s b3 b4 b6).equivAwayAdjoinRoot
  exact Algebra.Smooth.comp R R[X] _

/-- The divided chart has finite presentation over its original coefficient ring. -/
instance dividedCoordinate_finitePresentation :
    Algebra.FinitePresentation R (Coordinate W s b3 b4 b6) :=
  Algebra.FinitePresentation.trans R R[X] _

/-- The divided structure morphism is locally of finite presentation. -/
instance dividedStructure_finitePresentation :
    LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom
      (algebraMap R (Coordinate W s b3 b4 b6)))) :=
  (LocallyOfFinitePresentation.SpecMap_iff _).mpr
    (RingHom.finitePresentation_algebraMap.mpr inferInstance)

/-- Every point of the derivative open is relatively smooth in the same divided chart. -/
theorem verticalDerivative_range_smooth :
    Set.range (PrincipalAffineRefinement.inclusion (verticalDerivative W s b3 b4 b6)) ⊆
      (Spec.map (CommRingCat.ofHom
        (algebraMap R (Coordinate W s b3 b4 b6)))).smoothLocus := by
  let i := PrincipalAffineRefinement.inclusion (verticalDerivative W s b3 b4 b6)
  let q := Spec.map (CommRingCat.ofHom (algebraMap R (Coordinate W s b3 b4 b6)))
  have hi : i ≫ q = Spec.map (CommRingCat.ofHom
      (algebraMap R (Localization.Away (verticalDerivative W s b3 b4 b6)))) := by
    change Spec.map _ ≫ Spec.map _ = _
    rw [← Spec.map_comp]
    rfl
  let _ : Smooth (i ≫ q) := by
    rw [hi]
    exact (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
      (RingHom.smooth_algebraMap.mpr (verticalLocalization_smooth W s b3 b4 b6))
  rintro _ ⟨z, rfl⟩
  have h := Scheme.Hom.preimage_smoothLocus_eq i q
  rw [Scheme.Hom.smoothLocus_eq_top (i ≫ q)] at h
  exact h.ge (Set.mem_univ z)

/-- A field-valued divided input with nonzero vertical derivative is relatively smooth. -/
theorem dividedFieldPoint_range_smooth {K : Type u} [Field K] [Algebra R K]
    (a : Coordinate W s b3 b4 b6 →ₐ[R] K)
    (ha : a (verticalDerivative W s b3 b4 b6) ≠ 0) :
    Set.range (Spec.map (CommRingCat.ofHom a.toRingHom)) ⊆
      (Spec.map (CommRingCat.ofHom
        (algebraMap R (Coordinate W s b3 b4 b6)))).smoothLocus := by
  let g : Localization.Away (verticalDerivative W s b3 b4 b6) →+* K :=
    IsLocalization.Away.lift _ (isUnit_iff_ne_zero.mpr ha)
  have hg : Spec.map (CommRingCat.ofHom g) ≫
      PrincipalAffineRefinement.inclusion (verticalDerivative W s b3 b4 b6) =
        Spec.map (CommRingCat.ofHom a.toRingHom) := by
    rw [PrincipalAffineRefinement.inclusion, ← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext (IsLocalization.Away.lift_comp _ (isUnit_iff_ne_zero.mpr ha))
  rw [← hg]
  rintro _ ⟨z, rfl⟩
  exact verticalDerivative_range_smooth W s b3 b4 b6
    ⟨Spec.map (CommRingCat.ofHom g) z, rfl⟩

end FLT.Mazur.WeierstrassDilatation
