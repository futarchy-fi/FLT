/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassIncidenceShearConicCoefficient
public import FLT.Mazur.WeierstrassModificationXFiberConicOpen
public import FLT.Mazur.PrincipalOpenTensorGeometry
public import FLT.Mazur.PrincipalOpenTransportGeometry

/-!
# The entire original initial tensor boundary after coefficient shear

The full incidence open is identified with the full conic incidence open,
retaining every original tensor function and its original inclusion.
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
local notation "tx" => (1 : S) ⊗ₜ[R] t W s b3 b4 b6
local notation "B" => Localization.Away (conicT a c)
local notation "e" => tensorShearNormalEquiv W s b3 b4 b6 S r hs h3 h4 hr
local notation "f" => tensorShearInitialConicMap W s b3 b4 b6 S r hs h3 h4 hr

/-- The whole initial tensor incidence open is the whole conic incidence open. -/
def tensorShearInitialConicOpenEquiv : Localization.Away tx ≃ₐ[S] B :=
  (PrincipalOpenTransport.equiv (A := T₀) e tx (fiberT a c)
    (tensorShearNormalEquiv_t W s b3 b4 b6 S r hs h3 h4 hr)).trans
      (fiberConicOpenEquiv a c)

/-- Every original initial tensor function keeps its full conic restriction. -/
theorem tensorShearInitialConicOpenEquiv_base (z : T₀) :
    tensorShearInitialConicOpenEquiv W s b3 b4 b6 S r hs h3 h4 hr
      (algebraMap T₀ (Localization.Away tx) z) = algebraMap (ConicCoordinate a c) B (f z) := by
  rw [tensorShearInitialConicOpenEquiv, AlgEquiv.trans_apply,
    PrincipalOpenTransport.equiv_base]
  exact fiberOpenToConic_base a c (e z)

/-- The full original initial boundary as an isomorphism of principal spectra. -/
def tensorShearInitialConicBoundaryIso : Spec (.of B) ≅ Spec (.of (Localization.Away tx)) :=
  Scheme.Spec.mapIso (tensorShearInitialConicOpenEquiv W s b3 b4 b6 S r hs h3 h4 hr
    ).toRingEquiv.toCommRingCatIso.op

/-- The complete boundary comparison preserves the original tensor inclusion. -/
@[reassoc] theorem tensorShearInitialConicBoundaryIso_inclusion :
    (tensorShearInitialConicBoundaryIso W s b3 b4 b6 S r hs h3 h4 hr).hom ≫
      PrincipalOpenTensor.inclusion S (t W s b3 b4 b6) =
    PrincipalOpenTransport.inclusion (conicT a c) ≫
      Spec.map (CommRingCat.ofHom (f).toRingHom) := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext (tensorShearInitialConicOpenEquiv_base W s b3 b4 b6 S r hs h3 h4 hr)

/-- The comparison is cartesian on the full original tensor boundary. -/
theorem tensorShearInitialConicBoundary_isPullback :
    IsPullback (tensorShearInitialConicBoundaryIso W s b3 b4 b6 S r hs h3 h4 hr).hom
      (PrincipalOpenTransport.inclusion (conicT a c))
      (PrincipalOpenTensor.inclusion S (t W s b3 b4 b6))
      (Spec.map (CommRingCat.ofHom (f).toRingHom)) :=
  by
    have hf : Spec.map (CommRingCat.ofHom (f).toRingHom) =
        fiberConicImmersion a c ≫
          (Scheme.Spec.mapIso (e).toRingEquiv.toCommRingCatIso.op).hom := by
      change Spec.map _ = Spec.map _ ≫ Spec.map _
      rw [← Spec.map_comp]
      rfl
    have : Mono (Spec.map (CommRingCat.ofHom (f).toRingHom)) := by
      rw [hf]
      infer_instance
    exact IsPullback.of_horiz_isIso_mono
      ⟨tensorShearInitialConicBoundaryIso_inclusion W s b3 b4 b6 S r hs h3 h4 hr⟩

end FLT.Mazur.WeierstrassModificationX
