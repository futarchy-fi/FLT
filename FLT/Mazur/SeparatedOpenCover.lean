/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
/-!
# Separatedness from the overlap graphs of an open cover

Test the diagonal on every ordered pair of charts. Closedness of the actual
intersection image suffices because the intersection map is an immersion.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u v
namespace FLT.Mazur.SeparatedOpenCover
set_option backward.isDefEq.respectTransparency false in
/-- Test separatedness on every pair of charts of an open cover. -/
theorem of_pairwise {X S : Scheme.{u}} (f : X ⟶ S) (U : X.OpenCover.{v})
    (h : ∀ i j, IsClosedImmersion (pullback.mapDesc (U.f i) (U.f j) f)) :
    IsSeparated f := by
  constructor
  apply IsZariskiLocalAtTarget.of_openCover (Scheme.Pullback.openCoverOfLeftRight U U f f)
  intro ij
  have hp := pullback_map_diagonal_isPullback (U.f ij.1) (U.f ij.2) f
  change IsClosedImmersion (pullback.snd (pullback.diagonal f)
    (pullback.map (U.f ij.1 ≫ f) (U.f ij.2 ≫ f) f f (U.f ij.1) (U.f ij.2)
      (𝟙 S) (Category.comp_id _) (Category.comp_id _)))
  have hi := h ij.1 ij.2
  exact (MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion
    hp.isoPullback.hom _).mp (by simpa using hi)
/-- Closed images of the overlap maps suffice, since these maps are immersions. -/
theorem of_pairwise_closed {X S : Scheme.{u}} (f : X ⟶ S) (U : X.OpenCover.{v})
    (h : ∀ i j, IsClosed (Set.range (pullback.mapDesc (U.f i) (U.f j) f))) :
    IsSeparated f :=
  of_pairwise f U fun i j ↦ IsClosedImmersion.of_isPreimmersion _ (h i j)
end FLT.Mazur.SeparatedOpenCover
