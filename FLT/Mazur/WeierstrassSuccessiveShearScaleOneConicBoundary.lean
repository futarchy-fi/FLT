/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveShearScaleOne
public import FLT.Mazur.WeierstrassModificationXFiberConicOpen
public import FLT.Mazur.WeierstrassSuccessiveXMiddleOverlap
public import FLT.Mazur.WeierstrassSuccessiveXTensorOverlap
public import FLT.Mazur.PrincipalOpenTensorGeometry
public import FLT.Mazur.PrincipalOpenTransportGeometry
public import FLT.Mazur.WeierstrassSuccessiveXMiddleComponents

/-!
# The complete first retained conic boundary at scale one

The entire original tensor incidence open is the conic incidence open.
This comparison uses the scale-one equation and keeps the genuine next transition.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassSuccessiveX
open WeierstrassDividedDepth WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (s π b3 b4 b6 : R)
  (S : Type u) [CommRing S] [Algebra R S] (r : S)
  (hs : algebraMap R S s = 1) (hp : algebraMap R S π = 0)
  (h3 : algebraMap R S b3 = 0) (h4 : algebraMap R S b4 = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
local notation "U" => rootShearCurve (W.map (algebraMap R S)) r
local notation "a" => WeierstrassCurve.a₁ U
local notation "c" => algebraMap R S b6
local notation "T" => ScalarExtension W s π b3 b4 b6 S
local notation "C₀" => ConicCoordinate a c
local notation "B" => MiddleConicOpen U c
local notation "e" => tensorShearScaleOneFiberEquiv W s π b3 b4 b6 S r hs hp h3 h4 hr
local notation "t" => coord W s π b3 b4 b6 0
local notation "i" => PrincipalOpenTensor.inclusion S t

/-- Restrict the original scale-one tensor equation to its entire retained conic. -/
def tensorShearScaleOneConicMap : T →ₐ[S] C₀ := (fiberConicMap a c).comp (e).toAlgHom

local notation "f" => tensorShearScaleOneConicMap W s π b3 b4 b6 S r hs hp h3 h4 hr

/-- The original incidence and root-shifted slope survive on the full conic. -/
theorem tensorShearScaleOneConicMap_coord (k : Fin 3) :
    f (tensorCoord W s π b3 b4 b6 S k) =
      ![conicT a c, conicV a c + algebraMap S C₀ r, 0] k := by
  change fiberConicMap a c (e (tensorCoord W s π b3 b4 b6 S k)) = _
  rw [tensorShearScaleOneFiberEquiv_coord]
  fin_cases k
  · exact fiberConicMap_t a c
  · change fiberConicMap a c (fiberV a c + algebraMap S _ r) =
      conicV a c + algebraMap S C₀ r
    rw [map_add, fiberConicMap_v, AlgHom.commutes]
  · change fiberConicMap a c (fiberV a c ^ 2 +
      algebraMap S _ a * fiberV a c - algebraMap S _ c * fiberT a c ^ 2) = 0
    rw [map_sub, map_add, map_pow, map_mul, map_mul, map_pow, AlgHom.commutes,
      AlgHom.commutes, fiberConicMap_t, fiberConicMap_v]
    have h := conic_relation a c
    linear_combination h

/-- The whole actual tensor incidence open is the original full conic incidence open. -/
def tensorShearScaleOneConicOpenEquiv : TensorXOpen W s π b3 b4 b6 S ≃ₐ[S] B :=
  (PrincipalOpenTransport.equiv e (tensorCoord W s π b3 b4 b6 S 0)
    (fiberT a c) (tensorShearScaleOneFiberEquiv_coord W s π b3 b4 b6 S r
      hs hp h3 h4 hr 0)).trans (fiberConicOpenEquiv a c)

/-- The full open comparison retains every original tensor function. -/
theorem tensorShearScaleOneConicOpenEquiv_base (z : T) :
    tensorShearScaleOneConicOpenEquiv W s π b3 b4 b6 S r hs hp h3 h4 hr (algebraMap T _ z) =
      algebraMap C₀ B (f z) := by
  rw [tensorShearScaleOneConicOpenEquiv, AlgEquiv.trans_apply, PrincipalOpenTransport.equiv_base]
  exact fiberOpenToConic_base a c ((e) z)

/-- The actual original conic immersion, keeping the unsheared tensor coordinates. -/
def tensorShearScaleOneConicImmersion : Spec (.of C₀) ⟶ Spec (.of T) :=
  fiberConicImmersion a c ≫
    (Scheme.Spec.mapIso (e).toRingEquiv.toCommRingCatIso.op).hom

instance tensorShearScaleOneConicImmersion_mono :
    Mono (tensorShearScaleOneConicImmersion W s π b3 b4 b6 S r hs hp h3 h4 hr) :=
  inferInstanceAs (Mono (_ ≫ _))

/-- The conic immersion is induced by restriction of the original tensor functions. -/
theorem tensorShearScaleOneConicImmersion_eq_spec :
    tensorShearScaleOneConicImmersion W s π b3 b4 b6 S r hs hp h3 h4 hr =
      Spec.map (CommRingCat.ofHom (f).toRingHom) := by
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  rfl

/-- The entire original conic incidence boundary as an isomorphism of actual opens. -/
def tensorShearScaleOneConicBoundaryIso : Spec (.of B) ≅
    Spec (.of (TensorXOpen W s π b3 b4 b6 S)) :=
  Scheme.Spec.mapIso (tensorShearScaleOneConicOpenEquiv W s π b3 b4 b6 S r hs hp h3 h4 hr
    ).toRingEquiv.toCommRingCatIso.op

/-- The conic incidence boundary retains its original tensor inclusion. -/
@[reassoc] theorem tensorShearScaleOneConicBoundaryIso_inclusion :
    (tensorShearScaleOneConicBoundaryIso W s π b3 b4 b6 S r hs hp h3 h4 hr).hom ≫ i =
      PrincipalOpenTransport.inclusion (conicT a c) ≫
        tensorShearScaleOneConicImmersion W s π b3 b4 b6 S r hs hp h3 h4 hr := by
  rw [tensorShearScaleOneConicImmersion_eq_spec]
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  exact tensorShearScaleOneConicOpenEquiv_base W s π b3 b4 b6 S r hs hp h3 h4 hr

/-- This is the whole scheme intersection, with both original projections. -/
theorem tensorShearScaleOneConicBoundary_isPullback :
    IsPullback (tensorShearScaleOneConicBoundaryIso W s π b3 b4 b6 S r hs hp h3 h4 hr).hom
      (PrincipalOpenTransport.inclusion (conicT a c)) i
      (tensorShearScaleOneConicImmersion W s π b3 b4 b6 S r hs hp h3 h4 hr) :=
  IsPullback.of_horiz_isIso_mono
    ⟨tensorShearScaleOneConicBoundaryIso_inclusion W s π b3 b4 b6 S r hs hp h3 h4 hr⟩

/-- Compose with the genuine integral tensor transition to get the next divided open. -/
def tensorShearScaleOneDividedConicOpenEquiv : TensorDividedOpen W s π b3 b4 b6 S ≃ₐ[S] B :=
  (tensorOverlapEquiv W s π b3 b4 b6 S).trans
    (tensorShearScaleOneConicOpenEquiv W s π b3 b4 b6 S r hs hp h3 h4 hr)

/-- The comparison uses the actual transition on every localized original function. -/
theorem tensorShearScaleOneDividedConicOpenEquiv_transition
    (z : TensorDividedOpen W s π b3 b4 b6 S) :
    tensorShearScaleOneDividedConicOpenEquiv W s π b3 b4 b6 S r hs hp h3 h4 hr z =
      tensorShearScaleOneConicOpenEquiv W s π b3 b4 b6 S r hs hp h3 h4 hr
        (tensorOverlapEquiv W s π b3 b4 b6 S z) := rfl

end FLT.Mazur.WeierstrassSuccessiveX
