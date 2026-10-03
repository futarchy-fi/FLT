/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicNormalizationExact
public import FLT.Mazur.OneGonNormalizationTorus
public import FLT.Mazur.PolygonNormalizationTransport
public import FLT.Mazur.ModuleStalkExact
/-!
# The polygon normalization short exact sequence

The actual structure inclusion and zero-minus-adjacent-infinity branch
difference form a short exact sequence, for every positive polygon size and
every specified pinching cocone. The assertion includes the one-gon and two-gon.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
@[expose] public noncomputable section
universe u
namespace FLT.Mazur.PolygonNormalizationExact
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open PolygonPinching PolygonNormalizationComplex
variable (K : Type u) [Field K]
theorem atlas_shortExact (n : ℕ) [NeZero n] (hn : 0 < n) :
    (complex K n hn (PolygonAtlas.normalization K n) (PolygonAtlas.nodes K n)
      (PolygonAtlas.isPushout K n hn)).ShortExact := by
  rcases n with _ | (_ | n)
  · omega
  · exact OneGonNormalizationTorus.shortExact K
  · exact CyclicNormalizationChart.shortExact K (n + 2) (by omega)
variable (n : ℕ) [NeZero n] (hn : 0 < n) {C : Over (Spec (.of K))}
  (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
theorem shortExact : (complex K n hn p q h).ShortExact :=
  PolygonNormalizationTransport.shortExact K n hn p q h
    (PolygonAtlas.normalization K n) (PolygonAtlas.nodes K n)
    (PolygonAtlas.isPushout K n hn) (polygonIso K n hn p q h)
    (normalization_polygonIso K n hn p q h) (nodes_polygonIso K n hn p q h)
    (atlas_shortExact K n hn)
theorem abelianSheaf_shortExact :
    ((complex K n hn p q h).map (FCurve.CoherentDevissage.moduleToSheaf C.left)).ShortExact :=
  FCurve.CoherentDevissage.moduleToSheaf_shortExact (shortExact K n hn p q h)
end FLT.Mazur.PolygonNormalizationExact
