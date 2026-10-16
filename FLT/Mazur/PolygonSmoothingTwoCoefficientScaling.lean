/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonSmoothingIndependentScaling
public import FLT.Mazur.PolygonSmoothingScalingNaturality

/-!
# Exact extension criterion for two coefficient scalings

Away from order zero, two independently prescribed branch coefficients must
preserve the actual smoothing equation. That equation is sufficient as well:
it constructs an automorphism of the entire nonreduced chart with an explicit
inverse. This separates a closed-fiber correction from a lift of that correction.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.PolygonSmoothing
open CategoryTheory
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (t : R) (a b : Rˣ)

/-- Any full-chart map with the two prescribed weights preserves their product times t. -/
theorem twoCoefficientScale_necessary (f : ChartRing t →ₐ[R] ChartRing t)
    (hx : f (leftCoordinate t) = algebraMap R _ a * leftCoordinate t)
    (hy : f (rightCoordinate t) = algebraMap R _ b * rightCoordinate t) :
    (a : R) * b * t = t := by
  have h := congrArg f (coordinate_relation t)
  rw [map_mul, hx, hy, mul_mul_mul_comm, coordinate_relation,
    ← map_mul, ← map_mul, AlgHom.commutes] at h
  have he := congrArg (markedEvaluation t 1) h
  simpa only [AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply] using he

variable (h : (a : R) * b * t = t)

/-- Preserve the whole smoothing ring under the exact two-coefficient relation. -/
def twoCoefficientScale : ChartRing t →ₐ[R] ChartRing t :=
  evaluate t (algebraMap R _ a * leftCoordinate t)
    (algebraMap R _ b * rightCoordinate t) (by
      rw [mul_mul_mul_comm, coordinate_relation, ← map_mul, ← map_mul, h])

/-- The full first coordinate has its specified coefficient. -/
@[simp] theorem twoCoefficientScale_left :
    twoCoefficientScale t a b h (leftCoordinate t) =
      algebraMap R _ a * leftCoordinate t := evaluate_left ..

/-- The full second coordinate has its independently specified coefficient. -/
@[simp] theorem twoCoefficientScale_right :
    twoCoefficientScale t a b h (rightCoordinate t) =
      algebraMap R _ b * rightCoordinate t := evaluate_right ..

include h in
/-- The inverse coefficients preserve exactly the same parameter. -/
theorem twoCoefficientScale_inverse_relation : (↑a⁻¹ : R) * ↑b⁻¹ * t = t := by
  calc
    _ = (↑a⁻¹ : R) * ↑b⁻¹ * ((a : R) * b * t) := by rw [h]
    _ = t := by
      calc
        _ = ((↑a⁻¹ : R) * a) * ((↑b⁻¹ : R) * b) * t := by ring
        _ = t := by rw [Units.inv_mul, Units.inv_mul, one_mul, one_mul]

/-- The constructed two-coefficient map is an actual automorphism of the full chart. -/
def twoCoefficientScaleEquiv : ChartRing t ≃ₐ[R] ChartRing t :=
  { twoCoefficientScale t a b h with
    invFun := twoCoefficientScale t a⁻¹ b⁻¹ (twoCoefficientScale_inverse_relation t a b h)
    left_inv := fun x ↦ by
      have he :
          (twoCoefficientScale t a⁻¹ b⁻¹ (twoCoefficientScale_inverse_relation t a b h)).comp
            (twoCoefficientScale t a b h) = AlgHom.id R (ChartRing t) := by
        apply chartRing_hom_ext t <;> simp <;> simp [← mul_assoc, ← map_mul]
      exact DFunLike.congr_fun he x
    right_inv := fun x ↦ by
      have he : (twoCoefficientScale t a b h).comp
          (twoCoefficientScale t a⁻¹ b⁻¹ (twoCoefficientScale_inverse_relation t a b h)) =
            AlgHom.id R (ChartRing t) := by
        apply chartRing_hom_ext t <;> simp <;> simp [← mul_assoc, ← map_mul]
      exact DFunLike.congr_fun he x }

omit h in
/-- A full-chart extension exists exactly when the original smoothing equation is preserved. -/
theorem twoCoefficientScale_exists_iff :
    (∃ f : ChartRing t →ₐ[R] ChartRing t,
      f (leftCoordinate t) = algebraMap R _ a * leftCoordinate t ∧
      f (rightCoordinate t) = algebraMap R _ b * rightCoordinate t) ↔
        (a : R) * b * t = t := by
  constructor
  · rintro ⟨f, hx, hy⟩
    exact twoCoefficientScale_necessary t a b f hx hy
  · intro ht
    exact ⟨twoCoefficientScale t a b ht,
      twoCoefficientScale_left t a b ht, twoCoefficientScale_right t a b ht⟩

omit h in
/-- The previously constructed independent scaling is precisely the zero-parameter instance. -/
theorem twoCoefficientScale_zero (ht : t = 0) :
    twoCoefficientScale t a b (by rw [ht, mul_zero]) = independentScale t ht a b := by
  apply chartRing_hom_ext t <;> simp

/-- The two weights give a scheme automorphism over the unchanged nonreduced parameter. -/
def twoCoefficientScalingIso : chart R t ≅ chart R t :=
  AlgebraicGeometry.Scheme.Spec.mapIso
    (twoCoefficientScaleEquiv t a b h).toRingEquiv.toCommRingCatIso.op

end FLT.Mazur.PolygonSmoothing

namespace FLT.Mazur.PolygonSmoothing
open CategoryTheory AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
universe u
variable {R S : Type u} [CommRing R] [CommRing S]
  (f : R →+* S) (t : R) (s : S) (hs : f t = s) (a b : Rˣ)
  (h : (a : R) * b * t = t)

include hs h in
/-- The exact smoothing constraint is preserved by the original coefficient map. -/
theorem twoCoefficientScale_map_relation :
    (↑(Units.map f.toMonoidHom a) : S) *
      (↑(Units.map f.toMonoidHom b) : S) * s = s := by
  change f (a : R) * f (b : R) * s = s
  rw [← hs, ← map_mul, ← map_mul, h]

/-- Full coefficient substitution commutes with the constructed two-weight automorphism. -/
theorem ringMap_twoCoefficientScale :
    (ringMap f t s hs).comp (twoCoefficientScale t a b h).toRingHom =
      (twoCoefficientScale s (Units.map f.toMonoidHom a) (Units.map f.toMonoidHom b)
        (twoCoefficientScale_map_relation f t s hs a b h)).toRingHom.comp (ringMap f t s hs) := by
  apply chartRing_ringHom_ext
  · intro r
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      AlgHom.commutes, ringMap_scalar]
  · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      twoCoefficientScale_left, ringMap_left, map_mul, ringMap_scalar, Units.coe_map]
    rfl
  · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      twoCoefficientScale_right, ringMap_right, map_mul, ringMap_scalar, Units.coe_map]
    rfl

/-- The entire scheme square uses the explicit original node coefficient homomorphism. -/
@[reassoc] theorem twoCoefficientScalingIso_ringMap :
    (twoCoefficientScalingIso s (Units.map f.toMonoidHom a) (Units.map f.toMonoidHom b)
        (twoCoefficientScale_map_relation f t s hs a b h)).hom ≫
      Spec.map (CommRingCat.ofHom (ringMap f t s hs)) =
        Spec.map (CommRingCat.ofHom (ringMap f t s hs)) ≫
          (twoCoefficientScalingIso t a b h).hom := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg Spec.map (CommRingCat.hom_ext (ringMap_twoCoefficientScale f t s hs a b h).symm)

end FLT.Mazur.PolygonSmoothing
