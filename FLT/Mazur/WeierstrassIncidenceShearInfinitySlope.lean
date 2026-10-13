/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassIncidenceShearInfinityBoundary
public import FLT.Mazur.WeierstrassModificationXFiberShiftedInfinity

/-!
# The complete original initial infinity open on the shifted slope line

Compose the full tensor comparison with the entire shifted incidence-localization
equivalence. Every original fiber function and the full inclusion are retained.
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

local notation "P" => Localization.Away
  (slopePolynomial a * (Polynomial.X + Polynomial.C r))

/-- The entire original tensor infinity boundary is the full shifted slope localization. -/
def tensorShearInitialInfinitySlopeEquiv : Localization.Away y₀ ≃ₐ[S] P :=
  (tensorShearInitialInfinityEquiv W s b3 b4 b6 S r hs h3 h4 hr).trans
    (fiberShiftedInfinitySlopeEquiv a c r)

/-- The slope comparison keeps the restriction of every original tensor function. -/
theorem tensorShearInitialInfinitySlopeEquiv_base (w : T₀) :
    tensorShearInitialInfinitySlopeEquiv W s b3 b4 b6 S r hs h3 h4 hr
      (algebraMap T₀ (Localization.Away y₀) w) =
        algebraMap (Polynomial S) P (fiberIncidenceMap a c (e w)) := by
  rw [tensorShearInitialInfinitySlopeEquiv, AlgEquiv.trans_apply,
    tensorShearInitialInfinityEquiv_base, fiberShiftedInfinitySlopeEquiv_base]

/-- The complete original tensor boundary spectrum with its shifted slope coordinate. -/
def tensorShearInitialInfinitySlopeIso : Spec (.of P) ≅ Spec (.of (Localization.Away y₀)) :=
  Scheme.Spec.mapIso (tensorShearInitialInfinitySlopeEquiv W s b3 b4 b6 S r hs h3 h4 hr
    ).toRingEquiv.toCommRingCatIso.op

/-- The full boundary inclusion factors through the entire original incidence line. -/
@[reassoc] theorem tensorShearInitialInfinitySlopeIso_inclusion :
    (tensorShearInitialInfinitySlopeIso W s b3 b4 b6 S r hs h3 h4 hr).hom ≫
      PrincipalOpenTensor.inclusion S (y W s b3 b4 b6) =
        Spec.map (CommRingCat.ofHom (algebraMap (Polynomial S) P)) ≫
          fiberIncidenceImmersion a c ≫
            (Scheme.Spec.mapIso (e).toRingEquiv.toCommRingCatIso.op).hom := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext
    (RingHom.ext (tensorShearInitialInfinitySlopeEquiv_base W s b3 b4 b6 S r hs h3 h4 hr))

end FLT.Mazur.WeierstrassModificationX
