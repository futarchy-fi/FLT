/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicHomNormalizedGeometricOrbit
public import FLT.Mazur.OddWeierstrassCyclicHomNormalizedGeometricOrbit
public import FLT.Mazur.CyclicCharacteristicProductParameterGroupoid

/-!
# Geometric same-chart comparisons are finite relabeling orbits

This applies to every point of the full same-chart comparison scheme. It
identifies its endpoints and does not discard stabilizers or infinitesimal arrows.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] {K : Type} [Field K] [IsAlgClosed K]
  (b : Bool) (q r : Spec (.of K) ⟶ normalizedLocus n b)

/-- Geometric fibers in either actual normalized chart are common finite relabeling orbits. -/
theorem normalizedModuliMap_geometric_orbit
    (h : (normalizedModuliMap n b).app (Opposite.op (Spec (.of K))) (ULift.up q) =
      (normalizedModuliMap n b).app (Opposite.op (Spec (.of K))) (ULift.up r)) :
    ∃ e : RelabelGroup n, q ≫ (normalizedRelabelAction n b e).hom = r := by
  cases b
  · obtain ⟨a, c, he⟩ :=
      UniversalWeierstrass.cyclicHomNormalizedModuliMap_geometric_orbit n q r h
    exact ⟨⟨a, 1, c⟩, he⟩
  · obtain ⟨a, c, he⟩ :=
      OddWeierstrassParameter.cyclicHomNormalizedModuliMap_geometric_orbit n q r h
    exact ⟨⟨1, a, c⟩, he⟩

/-- Every given full geometric same-chart comparison identifies its endpoints up to relabeling. -/
theorem compatible_geometric_sameChart_orbit
    (a : CompatibleIso ((normalizedSubgroup n b).baseChange q)
      ((normalizedSubgroup n b).baseChange r)) :
    ∃ e : RelabelGroup n, q ≫ (normalizedRelabelAction n b e).hom = r := by
  apply normalizedModuliMap_geometric_orbit
  rw [normalizedModuliMap_eq_pullback, normalizedModuliMap_eq_pullback]
  exact Quotient.sound ⟨a⟩

/-- The full actual same-chart arrow scheme has geometrically relabeled endpoints. -/
theorem productArrow_geometric_sameChart_orbit (a : ProductArrow n q r) :
    ∃ e : RelabelGroup n, q ≫ (normalizedRelabelAction n b e).hom = r :=
  compatible_geometric_sameChart_orbit n b q r (productCompatibleTestComparison n b b q r a)

end FLT.Mazur.CyclicCharacteristicAtlas
