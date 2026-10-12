/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveShearComponents
public import FLT.Mazur.WeierstrassSuccessiveXMiddleOverlap
public import FLT.Mazur.WeierstrassSuccessiveXTensorOverlap
public import FLT.Mazur.PrincipalOpenTensorGeometry
public import FLT.Mazur.PrincipalOpenTransportGeometry
public import FLT.Mazur.WeierstrassSuccessiveXMiddleComponents

/-!
# The complete original tensor incidence boundary after tangent shear

Localize the original tensor equation at its retained incidence function.
The full open is the conic incidence open, and tensoring the original overlap
identifies it with the actual next divided boundary, retaining every function.
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
  (hs : algebraMap R S s = 0) (hp : algebraMap R S π = 0)
  (h3 : algebraMap R S b3 = 0) (h4 : algebraMap R S b4 = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
local notation "U" => rootShearCurve (W.map (algebraMap R S)) r
local notation "a" => WeierstrassCurve.a₁ U
local notation "c" => algebraMap R S b6
local notation "T" => ScalarExtension W s π b3 b4 b6 S
local notation "C₀" => ConicCoordinate a c
local notation "B" => MiddleConicOpen U c
local notation "e" => tensorShearMiddleEquiv W s π b3 b4 b6 S r hs hp h3 h4
local notation "h2" => coefficientShear_a₂_zero W S r hr
local notation "f" => tensorShearConicMap W s π b3 b4 b6 S r hs hp h3 h4 hr
local notation "t" => coord W s π b3 b4 b6 0
local notation "i" => PrincipalOpenTensor.inclusion S t

/-- The whole actual tensor incidence open is the original full conic incidence open. -/
def tensorShearConicOpenEquiv : TensorXOpen W s π b3 b4 b6 S ≃ₐ[S] B :=
  (PrincipalOpenTransport.equiv e (tensorCoord W s π b3 b4 b6 S 0)
    (coord U 0 0 0 0 c 0) (tensorShearMiddleEquiv_coord W s π b3 b4 b6 S r hs hp h3 h4 0)
      ).trans (middleOverlapConicEquiv U c h2)

/-- The full open comparison retains every original tensor function. -/
theorem tensorShearConicOpenEquiv_base (z : T) :
    tensorShearConicOpenEquiv W s π b3 b4 b6 S r hs hp h3 h4 hr (algebraMap T _ z) =
      algebraMap C₀ B (f z) := by
  rw [tensorShearConicOpenEquiv, AlgEquiv.trans_apply, PrincipalOpenTransport.equiv_base]
  exact middleOverlapToConic_base U c h2 ((e) z)

/-- The actual original conic immersion, keeping the unsheared tensor coordinates. -/
def tensorShearConicImmersion : Spec (.of C₀) ⟶ Spec (.of T) :=
  middleConicImmersion U c h2 ≫
    (Scheme.Spec.mapIso (e).toRingEquiv.toCommRingCatIso.op).hom

instance tensorShearConicImmersion_mono :
    Mono (tensorShearConicImmersion W s π b3 b4 b6 S r hs hp h3 h4 hr) :=
  inferInstanceAs (Mono (_ ≫ _))

/-- The conic immersion is induced by restriction of the original tensor functions. -/
theorem tensorShearConicImmersion_eq_spec :
    tensorShearConicImmersion W s π b3 b4 b6 S r hs hp h3 h4 hr =
      Spec.map (CommRingCat.ofHom (f).toRingHom) := by
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  rfl

/-- The entire original conic incidence boundary as an isomorphism of actual opens. -/
def tensorShearConicBoundaryIso : Spec (.of B) ≅
    Spec (.of (TensorXOpen W s π b3 b4 b6 S)) :=
  Scheme.Spec.mapIso (tensorShearConicOpenEquiv W s π b3 b4 b6 S r hs hp h3 h4 hr
    ).toRingEquiv.toCommRingCatIso.op

/-- The conic incidence boundary retains its original tensor inclusion. -/
@[reassoc] theorem tensorShearConicBoundaryIso_inclusion :
    (tensorShearConicBoundaryIso W s π b3 b4 b6 S r hs hp h3 h4 hr).hom ≫ i =
      PrincipalOpenTransport.inclusion (conicT a c) ≫
        tensorShearConicImmersion W s π b3 b4 b6 S r hs hp h3 h4 hr := by
  rw [tensorShearConicImmersion_eq_spec]
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  exact tensorShearConicOpenEquiv_base W s π b3 b4 b6 S r hs hp h3 h4 hr

/-- This is the whole scheme intersection, with both original projections. -/
theorem tensorShearConicBoundary_isPullback :
    IsPullback (tensorShearConicBoundaryIso W s π b3 b4 b6 S r hs hp h3 h4 hr).hom
      (PrincipalOpenTransport.inclusion (conicT a c)) i
      (tensorShearConicImmersion W s π b3 b4 b6 S r hs hp h3 h4 hr) :=
  IsPullback.of_horiz_isIso_mono
    ⟨tensorShearConicBoundaryIso_inclusion W s π b3 b4 b6 S r hs hp h3 h4 hr⟩

/-- Compose with the genuine integral tensor transition to get the next divided open. -/
def tensorShearDividedConicOpenEquiv : TensorDividedOpen W s π b3 b4 b6 S ≃ₐ[S] B :=
  (tensorOverlapEquiv W s π b3 b4 b6 S).trans
    (tensorShearConicOpenEquiv W s π b3 b4 b6 S r hs hp h3 h4 hr)

/-- The comparison uses the actual transition on every localized original function. -/
theorem tensorShearDividedConicOpenEquiv_transition (z : TensorDividedOpen W s π b3 b4 b6 S) :
    tensorShearDividedConicOpenEquiv W s π b3 b4 b6 S r hs hp h3 h4 hr z =
      tensorShearConicOpenEquiv W s π b3 b4 b6 S r hs hp h3 h4 hr
        (tensorOverlapEquiv W s π b3 b4 b6 S z) := rfl

end FLT.Mazur.WeierstrassSuccessiveX
