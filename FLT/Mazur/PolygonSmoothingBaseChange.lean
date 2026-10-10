/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonSmoothingSpecialFiber
public import FLT.Mazur.HilbertPolynomialQuotientBaseChange
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Actual base change of arithmetic polygon smoothing charts

The equation xy = t extends under every coefficient-ring map. The tensor
comparison preserves both named coordinates, and its spectrum identifies
the actual scheme pullback. Flatness of the coefficient change is not required.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

namespace FLT.Mazur.PolygonSmoothing

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

/-- Coefficient extension carries the original smoothing ideal to the new smoothing ideal. -/
theorem relationIdeal_map (t : R) :
    (relationIdeal t).map (MvPolynomial.map (algebraMap R S)) =
      relationIdeal (algebraMap R S t) := by
  simp only [relationIdeal, Ideal.map_span, Set.image_singleton, relation, map_sub,
    map_mul, MvPolynomial.map_X, MvPolynomial.map_C]

/-- The actual tensor base change of the arithmetic node chart. -/
def baseChangeEquiv (t : R) :
    S ⊗[R] ChartRing t ≃ₐ[S] ChartRing (algebraMap R S t) :=
  (HilbertChart.polynomialQuotientBaseChangeEquiv (Fin 2) R S (relationIdeal t)).trans
    (Ideal.quotientEquivAlgOfEq S (relationIdeal_map R S t))

/-- Tensor base change retains the original first branch coordinate. -/
theorem baseChangeEquiv_left (t : R) :
    baseChangeEquiv R S t (1 ⊗ₜ[R] leftCoordinate t) =
      leftCoordinate (algebraMap R S t) := by
  rw [leftCoordinate, baseChangeEquiv, AlgEquiv.trans_apply,
    HilbertChart.polynomialQuotientBaseChangeEquiv_tmul, MvPolynomial.map_X, one_smul,
    Ideal.quotientEquivAlgOfEq_mk]
  rfl

/-- Tensor base change retains the original second branch coordinate. -/
theorem baseChangeEquiv_right (t : R) :
    baseChangeEquiv R S t (1 ⊗ₜ[R] rightCoordinate t) =
      rightCoordinate (algebraMap R S t) := by
  rw [rightCoordinate, baseChangeEquiv, AlgEquiv.trans_apply,
    HilbertChart.polynomialQuotientBaseChangeEquiv_tmul, MvPolynomial.map_X, one_smul,
    Ideal.quotientEquivAlgOfEq_mk]
  rfl

attribute [local irreducible] baseChangeEquiv

/-- The actual map extending coefficients in the smoothing chart algebra. -/
def coefficientMap (t : R) : ChartRing t →+* ChartRing (algebraMap R S t) :=
  (baseChangeEquiv R S t).toRingHom.comp
    (Algebra.TensorProduct.includeRight : ChartRing t →ₐ[R] S ⊗[R] ChartRing t).toRingHom

/-- Coefficient extension preserves the first actual branch coordinate. -/
@[simp] theorem coefficientMap_left (t : R) :
    coefficientMap R S t (leftCoordinate t) = leftCoordinate (algebraMap R S t) :=
  baseChangeEquiv_left R S t

/-- Coefficient extension preserves the second actual branch coordinate. -/
@[simp] theorem coefficientMap_right (t : R) :
    coefficientMap R S t (rightCoordinate t) = rightCoordinate (algebraMap R S t) :=
  baseChangeEquiv_right R S t

/-- The smoothing chart over the new coefficients is the actual original scheme pullback. -/
def chartBaseChangeIso (t : R) :
    pullback (Spec.map (CommRingCat.ofHom (algebraMap R S))) (chartStructure R t) ≅
      chart S (algebraMap R S t) :=
  pullbackSpecIso R S (ChartRing t) ≪≫
    Scheme.Spec.mapIso (baseChangeEquiv R S t).symm.toRingEquiv.toCommRingCatIso.op

/-- The new structure morphism is the first actual pullback projection. -/
@[reassoc] theorem chartBaseChangeIso_inv_fst (t : R) :
    (chartBaseChangeIso R S t).inv ≫ pullback.fst _ _ =
      chartStructure S (algebraMap R S t) := by
  change Spec.map (CommRingCat.ofHom (baseChangeEquiv R S t).toRingHom) ≫
    (pullbackSpecIso R S (ChartRing t)).inv ≫ pullback.fst _ _ = _
  rw [pullbackSpecIso_inv_fst', ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  exact (baseChangeEquiv R S t).toAlgHom.comp_algebraMap

/-- The second pullback projection is precisely the original coefficient-extension map. -/
@[reassoc] theorem chartBaseChangeIso_inv_snd (t : R) :
    (chartBaseChangeIso R S t).inv ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (coefficientMap R S t)) := by
  change Spec.map (CommRingCat.ofHom (baseChangeEquiv R S t).toRingHom) ≫
    (pullbackSpecIso R S (ChartRing t)).inv ≫ pullback.snd _ _ = _
  rw [pullbackSpecIso_inv_snd, ← Spec.map_comp]
  rfl

end FLT.Mazur.PolygonSmoothing
