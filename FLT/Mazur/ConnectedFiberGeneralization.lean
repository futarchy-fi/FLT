/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LocalClosedFiberConnectedness
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.RingTheory.Spectrum.Prime.ConstructibleSet

/-!
# The actual connected fiber locus is stable under generalization

A connected fiber makes the entire stalk base change geometrically connected.
Its image is exactly the set of generalizations of that base point. This proves
stability under generalization for the actual fiber locus on a locally
Noetherian base; constructibility or an independent neighborhood argument is
still needed to deduce openness.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry Topology
namespace FLT.Mazur.Approximation
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {X S : Scheme.{0}} [IsLocallyNoetherian S]
  (f : X ⟶ S) [IsProper f] [Flat f] [GeometricallyReduced f]
  (s : S ⟶ X) (hs : s ≫ f = 𝟙 S)

include s hs in
/-- Connectedness at one point makes the actual stalk family geometrically connected. -/
theorem geometricallyConnected_stalk_baseChange (b : S)
    (hb : b ∈ geometricallyConnectedLocus f) :
    GeometricallyConnected (pullback.snd f (S.fromSpecStalk b)) := by
  let a := S.fromSpecStalk b
  let t := SchemeProperGeometricFiberSections.baseChangedSection f s hs a
  apply geometricallyConnected_of_spec_local_closedFiber (pullback.snd f a) t
    (SchemeProperGeometricFiberSections.baseChangedSection_projection f s hs a)
  rw [geometricallyConnectedLocus_of_isPullback (IsPullback.of_hasPullback f a)]
  change S.fromSpecStalk b (IsLocalRing.closedPoint (S.presheaf.stalk b)) ∈
    geometricallyConnectedLocus f
  rwa [Scheme.fromSpecStalk_closedPoint]

include s hs in
/-- The actual geometric connectedness locus is stable under generalization. -/
theorem stableUnderGeneralization_geometricallyConnectedLocus :
    StableUnderGeneralization (geometricallyConnectedLocus f) := by
  intro b c hcb hb
  let _ := geometricallyConnected_stalk_baseChange f s hs b hb
  apply range_subset_geometricallyConnectedLocus
    (IsPullback.of_hasPullback f (S.fromSpecStalk b))
  rw [Scheme.range_fromSpecStalk]
  exact hcb

/-- On an affine Noetherian base, constructibility is the remaining input for openness. -/
theorem isOpen_geometricallyConnectedLocus_of_constructible
    {R : CommRingCat.{0}} [IsNoetherianRing R] {Y : Scheme.{0}}
    (g : Y ⟶ Spec R) [IsProper g] [Flat g] [GeometricallyReduced g]
    (t : Spec R ⟶ Y) (ht : t ≫ g = 𝟙 _)
    (hcon : IsConstructible (geometricallyConnectedLocus g)) :
    IsOpen (geometricallyConnectedLocus g) :=
  PrimeSpectrum.isOpen_of_stableUnderGeneralization_of_isConstructible
    (stableUnderGeneralization_geometricallyConnectedLocus g t ht) hcon

end FLT.Mazur.Approximation
