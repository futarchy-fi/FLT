/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXFiberConicGeometry
public import FLT.Mazur.PrincipalOpenTransportGeometry

/-!
# The complete incidence open of the horizontal fiber

Inverting the incidence coordinate cancels its factor in the fiber equation.
The resulting equivalence retains the original closed conic immersion.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] (a c : R)
local notation "F" => FiberCoordinate a c
local notation "C₀" => ConicCoordinate a c
local notation "O" => Localization.Away (fiberT a c)
local notation "B" => Localization.Away (conicT a c)

/-- The conic equation holds on the whole incidence open of the original fiber. -/
theorem fiberOpen_conic_relation :
    algebraMap F O (fiberV a c) *
        (algebraMap F O (fiberV a c) + algebraMap R O a) -
      algebraMap R O c * algebraMap F O (fiberT a c) ^ 2 = 0 := by
  apply (IsLocalization.Away.algebraMap_isUnit (S := O) (fiberT a c)).mul_left_cancel
  have h := congrArg (algebraMap F O) (fiber_relation a c)
  simpa only [map_mul, map_sub, map_add, map_pow, map_zero,
    ← IsScalarTower.algebraMap_apply R F O, mul_zero] using h

/-- Restrict the original conic quotient to the full incidence open. -/
def fiberOpenToConic : O →ₐ[R] B :=
  IsLocalization.Away.liftAlgHom (fiberT a c)
    (f := (IsScalarTower.toAlgHom R C₀ B).comp (fiberConicMap a c)) (by
      change IsUnit (algebraMap C₀ B (fiberConicMap a c (fiberT a c)))
      rw [fiberConicMap_t]
      exact IsLocalization.Away.algebraMap_isUnit (S := B) _)

/-- The conic evaluates in the original fiber localization. -/
def conicToFiberOpen : C₀ →ₐ[R] O :=
  conicEvaluation a c (algebraMap F O (fiberT a c))
    (algebraMap F O (fiberV a c)) (fiberOpen_conic_relation a c)

/-- The inverse map keeps both original incidence and slope functions. -/
def conicOpenToFiber : B →ₐ[R] O :=
  IsLocalization.Away.liftAlgHom (conicT a c) (f := conicToFiberOpen a c) (by
    change IsUnit (conicEvaluation a c _ _ _ (conicT a c))
    rw [conicEvaluation_t]
    exact IsLocalization.Away.algebraMap_isUnit (S := O) _)

/-- Every fiber function restricts through the original conic quotient. -/
@[simp] theorem fiberOpenToConic_base (z : F) :
    fiberOpenToConic a c (algebraMap F O z) =
      algebraMap C₀ B (fiberConicMap a c z) := by
  rw [fiberOpenToConic, IsLocalization.Away.liftAlgHom_apply,
    IsLocalization.Away.lift_eq]
  rfl

/-- Every conic function retains its evaluation on the original fiber open. -/
@[simp] theorem conicOpenToFiber_base (z : C₀) :
    conicOpenToFiber a c (algebraMap C₀ B z) = conicToFiberOpen a c z := by
  rw [conicOpenToFiber, IsLocalization.Away.liftAlgHom_apply,
    IsLocalization.Away.lift_eq]
  rfl

/-- The entire fiber incidence open is exactly the entire conic incidence open. -/
def fiberConicOpenEquiv : O ≃ₐ[R] B := by
  apply AlgEquiv.ofAlgHom (fiberOpenToConic a c) (conicOpenToFiber a c)
  · apply IsLocalization.algHom_ext (Submonoid.powers (conicT a c))
    apply conic_hom_ext
    · change fiberOpenToConic a c
        (conicOpenToFiber a c (algebraMap C₀ B (conicT a c))) = _
      simp only [conicOpenToFiber_base, conicToFiberOpen, conicEvaluation_t,
        fiberOpenToConic_base, fiberConicMap_t]
      rfl
    · change fiberOpenToConic a c
        (conicOpenToFiber a c (algebraMap C₀ B (conicV a c))) = _
      simp only [conicOpenToFiber_base, conicToFiberOpen, conicEvaluation_v,
        fiberOpenToConic_base, fiberConicMap_v]
      rfl
  · apply IsLocalization.algHom_ext (Submonoid.powers (fiberT a c))
    apply fiber_hom_ext
    · change conicOpenToFiber a c
        (fiberOpenToConic a c (algebraMap F O (fiberT a c))) = _
      simp only [fiberOpenToConic_base, fiberConicMap_t, conicOpenToFiber_base,
        conicToFiberOpen, conicEvaluation_t]
      rfl
    · change conicOpenToFiber a c
        (fiberOpenToConic a c (algebraMap F O (fiberV a c))) = _
      simp only [fiberOpenToConic_base, fiberConicMap_v, conicOpenToFiber_base,
        conicToFiberOpen, conicEvaluation_v]
      rfl

/-- The full conic boundary as an isomorphism of the original principal spectra. -/
def fiberConicOpenIso : Spec (.of B) ≅ Spec (.of O) :=
  Scheme.Spec.mapIso (fiberConicOpenEquiv a c).toRingEquiv.toCommRingCatIso.op

/-- Both original inclusions are preserved on the whole open. -/
@[reassoc] theorem fiberConicOpenIso_inclusion :
    (fiberConicOpenIso a c).hom ≫ PrincipalOpenTransport.inclusion (fiberT a c) =
      PrincipalOpenTransport.inclusion (conicT a c) ≫ fiberConicImmersion a c := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext (fiberOpenToConic_base a c)

/-- The conic boundary square is cartesian without any reducedness assumption. -/
theorem fiberConicOpen_isPullback :
    IsPullback (fiberConicOpenIso a c).hom (PrincipalOpenTransport.inclusion (conicT a c))
      (PrincipalOpenTransport.inclusion (fiberT a c)) (fiberConicImmersion a c) :=
  IsPullback.of_horiz_isIso_mono ⟨fiberConicOpenIso_inclusion a c⟩

end FLT.Mazur.WeierstrassModificationX
