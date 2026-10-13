/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassIncidenceShearNormalForm
public import FLT.Mazur.WeierstrassModificationXScaleOneTensor
public import FLT.Mazur.WeierstrassModificationXFiberConicGeometry
public import FLT.Mazur.PrincipalOpenTensorGeometry
public import FLT.Mazur.PrincipalOpenTransportGeometry

/-!
# The full initial infinity boundary under arbitrary-root shear

The original vertical function is the conic factor times the root-shifted
slope. Its entire tensor localization retains that shift and every function.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
open scoped TensorProduct
namespace FLT.Mazur.WeierstrassModificationX
open WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (S : Type u) [CommRing S] [Algebra R S] (r : S)
  (hs : algebraMap R S s = 0) (h3 : algebraMap R S b3 = 0)
  (h4 : algebraMap R S b4 = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
local notation "a" => (rootShearCurve (W.map (algebraMap R S)) r).a₁
local notation "c" => algebraMap R S b6
local notation "T₀" => S ⊗[R] Coordinate W s b3 b4 b6
local notation "e" => tensorShearNormalEquiv W s b3 b4 b6 S r hs h3 h4 hr
local notation "f" => coefficientShearNormalEquiv W s b3 b4 b6 S r hs h3 h4 hr
local notation "q" => fiberConicFactor a c
local notation "z" => fiberV a c + algebraMap S (FiberCoordinate a c) r
local notation "y₀" => (1 : S) ⊗ₜ[R] y W s b3 b4 b6

/-- The actual horizontal cubic function is the full normal conic factor. -/
theorem tensorShearNormalEquiv_x : e ((1 : S) ⊗ₜ[R] x W s b3 b4 b6) = q := by
  change f (incidenceCoefficientShearEquiv W s b3 b4 b6 S r _) = _
  rw [incidenceCoefficientShearEquiv_tmul, one_smul, coefficientMap_x, shearForward_x]
  simp only [x, map_sub, map_add, map_mul, map_pow, AlgEquiv.commutes,
    coefficientShearNormalEquiv_v, coefficientShearNormalEquiv_t,
    coefficientShear_a₂_zero W S r hr, h3, h4, mul_zero, sub_zero, map_zero,
    zero_mul, add_zero, zero_add]
  dsimp only [fiberConicFactor]
  ring

/-- The entire vertical function retains the original root shift. -/
theorem tensorShearNormalEquiv_y : e y₀ = q * z := by
  have h : y₀ = ((1 : S) ⊗ₜ[R] x W s b3 b4 b6) *
      ((1 : S) ⊗ₜ[R] v W s b3 b4 b6) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, y]
  rw [h, map_mul, tensorShearNormalEquiv_x, tensorShearNormalEquiv_v]

/-- The whole original infinity localization is the shifted normal fiber localization. -/
def tensorShearInitialInfinityEquiv :
    Localization.Away y₀ ≃ₐ[S] Localization.Away (q * z) :=
  PrincipalOpenTransport.equiv (A := T₀) e y₀ (q * z)
    (tensorShearNormalEquiv_y W s b3 b4 b6 S r hs h3 h4 hr)

/-- Every function keeps its original restriction on the full infinity overlap. -/
theorem tensorShearInitialInfinityEquiv_base (w : T₀) :
    tensorShearInitialInfinityEquiv W s b3 b4 b6 S r hs h3 h4 hr
      (algebraMap T₀ (Localization.Away y₀) w) =
        algebraMap (FiberCoordinate a c) (Localization.Away (q * z)) (e w) :=
  PrincipalOpenTransport.equiv_base _ _ _ _ w

/-- The entire original tensor infinity boundary has the shifted normal spectrum. -/
def tensorShearInitialInfinityIso :
    Spec (.of (Localization.Away (q * z))) ≅ Spec (.of (Localization.Away y₀)) :=
  Scheme.Spec.mapIso (tensorShearInitialInfinityEquiv W s b3 b4 b6 S r hs h3 h4 hr
    ).toRingEquiv.toCommRingCatIso.op

/-- The exact infinity comparison preserves the inclusion of the full original tensor open. -/
@[reassoc] theorem tensorShearInitialInfinityIso_inclusion :
    (tensorShearInitialInfinityIso W s b3 b4 b6 S r hs h3 h4 hr).hom ≫
      PrincipalOpenTensor.inclusion S (y W s b3 b4 b6) =
        PrincipalOpenTransport.inclusion (q * z) ≫
          (Scheme.Spec.mapIso (e).toRingEquiv.toCommRingCatIso.op).hom := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext
    (RingHom.ext (tensorShearInitialInfinityEquiv_base W s b3 b4 b6 S r hs h3 h4 hr))

end FLT.Mazur.WeierstrassModificationX
