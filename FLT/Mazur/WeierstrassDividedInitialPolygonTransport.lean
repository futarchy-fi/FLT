/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedInitialPolygonMaps

/-!
# Explicit smoothing transport for full initial comparisons

An equality of smoothing parameters transports the complete initial chart.
The equality remains an explicit input; it does not identify different thicknesses.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
  (s t : R) [Fact (IsNilpotent t)] (hst : s = t) (k : ℕ)

/-- Transport the original full initial node only along a proved equality of smoothings. -/
def initialPolygonMapOfEq (b : Bool) : Spec (.of (PolynomialNodeOpen W s)) ⟶
    PolygonInfinitesimal.scheme R t (2 * k + 3) (by omega) := by
  subst s
  exact initialPolygonMap W t k b

instance initialPolygonMapOfEq_isOpenImmersion (b : Bool) :
    IsOpenImmersion (initialPolygonMapOfEq W s t hst k b) := by
  subst s
  exact initialPolygonMap_isOpenImmersion W t k b

variable {S : Type u} [CommRing S] (f : R →+* S)
  (U : WeierstrassCurve S) (s' t' : S) [Fact (IsNilpotent t')]
  (hW : W.map f = U) (hs : f s = s') (ht : f t = t') (hst' : s' = t')

/-- Explicit thickness equalities preserve every original coefficient and branch label. -/
@[reassoc] theorem initialPolygonMapOfEq_parameterProjection (b : Bool) :
    initialPolygonMapOfEq U s' t' hst' k b ≫
      PolygonInfinitesimal.parameterProjection f t t' ht (2 * k + 3) (by omega) =
    Spec.map (CommRingCat.ofHom (nodeOpenCoefficientRingMapTo f W s U s' hW hs)) ≫
      initialPolygonMapOfEq W s t hst k b := by
  subst s s'
  exact initialPolygonMap_parameterProjectionTo W t k f U t' hW ht b

end FLT.Mazur.WeierstrassDividedDepth
