/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicBoundaryLocusGenerator
public import FLT.Mazur.GroupSectionMarkingPullback

/-!
# Original cyclic subgroups give unrestricted closed tests fppf locally

The actual Cartier-generator cover constructs points of the closed boundary
locus relative to the original supplied curve. Full subgroup comparisons
retain the chosen generator and both independently given auxiliary markings.
This does not assert that the supplied curve parametrizes all singular families.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
open scoped CategoryTheory.Obj
namespace FLT.Mazur.CyclicBoundaryParameter
open GeneralizedEllipticCurve GroupSectionBaseChange
open UniversalWeierstrass (Labels)
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} (E : GeneralizedEllipticCurve S) (n : ℕ) [NeZero n]
  [SmoothOfRelativeDimension 1 E.group.hom] (H : E.FiniteSubgroup n) (hc : H.IsCyclic)
  (a : Labels 4 →* (𝟙_ (Over S) ⟶ E.group))
  (b : Labels 3 →* (𝟙_ (Over S) ⟶ E.group))

include hc in
/-- The actual generator cover gives closed tests with the full original subgroup and labels. -/
theorem exists_unrestricted_generator_test :
    ∃ (U : Scheme) (g : U ⟶ S), Flat g ∧ Surjective g ∧ LocallyOfFinitePresentation g ∧
      ∃ (P : 𝟙_ (Over U) ⟶ (H.baseChange g).carrier)
        (hP : (H.baseChange g).IsCartierGenerator P)
        (k : U ⟶ unrestrictedMultiplicationLocus E n)
        (d : FiniteSubgroup.CompatibleIso (H.baseChange g)
          ((unrestrictedLocusSubgroup E n).baseChange k)),
        (∀ j : Label n,
          (pullMarking g E a j.1 * pullMarking g E b j.2.1 *
              (H.baseChange g).generatorCurveMarking hP j.2.2) ≫ d.curve.hom.group =
            pullSection k (unrestrictedLocusLabel E n j)) ∧
        P ≫ d.subgroup.hom = pullSection k (unrestrictedLocusGenerator E n) := by
  obtain ⟨U, g, hf, hs, hl, P, hP⟩ := hc
  let A := pullMarking g E a
  let B := pullMarking g E b
  exact ⟨U, g, hf, hs, hl, P, hP, generatorLocusLift E n g (H.baseChange g) hP A B,
    generatorLocusSubgroupIso E n g (H.baseChange g) hP A B,
    generatorLocusSubgroupIso_label E n g (H.baseChange g) hP A B,
    generatorLocusSubgroupIso_generator E n g (H.baseChange g) hP A B⟩

include hc in
/-- In particular every original cyclic subgroup is locally the actual closed universal subgroup. -/
theorem exists_unrestricted_subgroup_test :
    ∃ (U : Scheme) (g : U ⟶ S), Flat g ∧ Surjective g ∧ LocallyOfFinitePresentation g ∧
      ∃ k : U ⟶ unrestrictedMultiplicationLocus E n,
        Nonempty (FiniteSubgroup.CompatibleIso (H.baseChange g)
          ((unrestrictedLocusSubgroup E n).baseChange k)) := by
  obtain ⟨U, g, hf, hs, hl, P, hP, k, d, _⟩ :=
    exists_unrestricted_generator_test E n H hc (1 : Labels 4 →* _) (1 : Labels 3 →* _)
  exact ⟨U, g, hf, hs, hl, k, ⟨d⟩⟩

end FLT.Mazur.CyclicBoundaryParameter
