/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonRefinedClosedCharts
public import FLT.Mazur.PolygonCubicTorusImmersion

/-!
# Global stalk surjectivity of the polygon cubic morphism

The refined node charts and the torus opens cover the polygon. On each of
these opens the actual cubic morphism is an immersion, so all its stalk maps
are surjective. This does not assert global injectivity.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.PolygonCubicSections
open PolygonPinching
attribute [local instance] MvPolynomial.gradedAlgebra
variable (K : Type) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
  (a : Fin n → Kˣ)

/-- Surjectivity of the cubic stalk map at every point in a torus open. -/
lemma torus_stalkMap_surjective (i : Fin n) (z : C.left)
    (hz : z ∈ torusOpen K n hn p q h i) :
    Function.Surjective ((cubicProjectiveMorphism K n hn p q h a).stalkMap z) := by
  have := torus_isImmersion K n hn p q h a i
  exact AffineRestrictionImmersion.stalkMap_surjective (torusOpen K n hn p q h i).ι
    (cubicProjectiveMorphism K n hn p q h a) ⟨z, hz⟩

/-- The split-node and torus cover proves all stalk maps surjective for n ≥ 2. -/
lemma split_surjectiveOnStalks (hn₂ : 2 ≤ n) :
    SurjectiveOnStalks (cubicProjectiveMorphism K n hn p q h a) := by
  constructor
  intro z
  rcases PolygonSplitCubicCoordinates.refinement_covers K n hn p q h a hn₂ z with
    ⟨i, hi⟩ | ⟨i, x, y, rfl⟩
  · exact torus_stalkMap_surjective K n hn p q h a i z hi
  · have := PolygonSplitCubicCoordinates.refinement_isImmersion K n hn p q h a hn₂ i x
    exact AffineRestrictionImmersion.stalkMap_surjective
      (PolygonSplitCubicCoordinates.refinementChart K n hn p q h a hn₂ i x)
      (cubicProjectiveMorphism K n hn p q h a) y

/-- The one-gon retains its node and has surjective cubic stalk maps everywhere. -/
lemma one_surjectiveOnStalks (hn : 0 < 1)
    {C : Over (Spec (.of K))} (p : components K 1 ⟶ C) (q : nodes K 1 ⟶ C)
    (h : IsPushout (toComponents K 1 hn) (toNodes K 1) p q) (a : Fin 1 → Kˣ) :
    SurjectiveOnStalks (cubicProjectiveMorphism K 1 hn p q h a) := by
  constructor
  intro z
  rcases PolygonOneGonCubicCoordinates.refinement_covers K hn p q h a z with
    ⟨i, hi⟩ | ⟨i, x, y, rfl⟩
  · exact torus_stalkMap_surjective K 1 hn p q h a i z hi
  · have := PolygonOneGonCubicCoordinates.refinement_isImmersion K hn p q h a x i
    exact AffineRestrictionImmersion.stalkMap_surjective
      (PolygonOneGonCubicCoordinates.refinementChart K hn p q h a x i)
      (cubicProjectiveMorphism K 1 hn p q h a) y

/-- The actual cubic morphism is surjective on stalks for every nonempty polygon. -/
theorem cubicProjectiveMorphism_surjectiveOnStalks :
    SurjectiveOnStalks (cubicProjectiveMorphism K n hn p q h a) := by
  by_cases he : n = 1
  · subst n
    exact one_surjectiveOnStalks K hn p q h a
  · exact split_surjectiveOnStalks K n hn p q h a (by omega)

end FLT.Mazur.PolygonCubicSections
