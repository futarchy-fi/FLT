/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ConnectedFiberGeneralization
public import FLT.Mazur.ConnectedFiberPrimeStratum
public import FLT.Mazur.NoetherianConstructibleCriterion

/-!
# Openness of geometrically connected fibers for proper smooth pointed families

The actual fiber locus is constructible by Noetherian induction on reduced
integral closed strata. Stability under generalization then proves openness.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry Topology TopologicalSpace
namespace FLT.Mazur.Approximation

variable {R : CommRingCat.{0}} [IsNoetherianRing R]
  {X : Scheme.{0}} (f : X ⟶ Spec R) [IsProper f] [Smooth f]
  (s : Spec R ⟶ X) (hs : s ≫ f = 𝟙 _)

include s hs in
/-- The actual connected-fiber locus is constructible over any Noetherian affine base. -/
theorem isConstructible_proper_smooth_connectedFiberLocus :
    IsConstructible (geometricallyConnectedLocus f) := by
  apply isConstructible_of_irreducible_closed_pieces
  intro Z hZ
  let p := PrimeSpectrum.vanishingIdeal (Z : Set (Spec R))
  let _ : p.IsPrime := PrimeSpectrum.isIrreducible_iff_vanishingIdeal_isPrime.mp hZ
  have heq : PrimeSpectrum.zeroLocus (p : Set R) = (Z : Set (Spec R)) := by
    rw [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, Z.isClosed.closure_eq]
  obtain ⟨U, hU, hn, hc⟩ := exists_connectedFiber_primeStratum_piece f s hs p
  exact ⟨U, hU, heq ▸ hn, heq ▸ hc⟩

include s hs in
/-- Proper smooth pointed families have an open actual geometrically connected fiber locus. -/
theorem isOpen_proper_smooth_connectedFiberLocus :
    IsOpen (geometricallyConnectedLocus f) := by
  let _ := geometricallyReduced_of_smooth f
  exact isOpen_geometricallyConnectedLocus_of_constructible f s hs
    (isConstructible_proper_smooth_connectedFiberLocus f s hs)

end FLT.Mazur.Approximation
