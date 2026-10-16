/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXInitialPolygonChart
public import FLT.Mazur.WeierstrassModificationXArithmeticRestrictionMaps

/-!
# The actual initial polygon comparison follows arithmetic quotient orders

The original full node quotient map commutes with the thick polygon comparison.
This holds for any original smoothing s, including s = π^start.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.WeierstrassModificationX
open PolygonArithmeticStages
set_option backward.isDefEq.respectTransparency false
universe u
variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
  (W : WeierstrassCurve R) (s : R) (U : WeierstrassCurve S) (s' : S)
  (hW : W.map f = U) (hs : f s = s')

/-- Independently named target coefficients preserve the same complete initial comparison. -/
@[reassoc] theorem initialPolygonChart_coefficientsTo :
    Spec.map (CommRingCat.ofHom (nodeOpenCoefficientRingMapTo f W s U s' hW hs)) ≫
      initialPolygonChart W s = initialPolygonChart U s' ≫
        Spec.map (CommRingCat.ofHom (PolygonSmoothing.ringMap f s s' hs)) := by
  subst U s'
  exact initialPolygonChart_coefficients W s f

variable (π : R) (m : ℕ)
local notation "Q₀" => Quotient R π m
local notation "Q₁" => Quotient R π (m + 1)
local notation "q₀" => algebraMap R Q₀
local notation "q₁" => algebraMap R Q₁

/-- The original full arithmetic initial neighborhood retains its exact smoothing thickness. -/
def arithmeticInitialPolygonChart :
    Spec (.of (PolynomialNodeOpen (W.map q₀) (q₀ s))) ⟶
      PolygonSmoothing.chart Q₀ (q₀ s) := initialPolygonChart (W.map q₀) (q₀ s)

instance arithmeticInitialPolygonChart_isOpenImmersion :
    IsOpenImmersion (arithmeticInitialPolygonChart W s π m) :=
  initialPolygonChart_isOpenImmersion _ _

/-- The original full initial quotient restriction commutes on every function. -/
@[reassoc] theorem arithmeticInitialPolygonChart_restriction :
    arithmeticFullInitialNodeQuotient R π m W s ≫
      arithmeticInitialPolygonChart W s π (m + 1) =
    arithmeticInitialPolygonChart W s π m ≫
      Spec.map (CommRingCat.ofHom (PolygonSmoothing.ringMap (restriction R π m).toRingHom
        (q₁ s) (q₀ s) ((restriction R π m).commutes s))) :=
  initialPolygonChart_coefficientsTo (restriction R π m).toRingHom (W.map q₁) (q₁ s)
    (W.map q₀) (q₀ s) (arithmeticInitialCurve_restriction R π m W)
    ((restriction R π m).commutes s)

end FLT.Mazur.WeierstrassModificationX
