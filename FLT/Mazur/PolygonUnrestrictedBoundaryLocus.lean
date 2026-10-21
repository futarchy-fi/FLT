/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicBoundaryOriginalTestCoverage
public import FLT.Mazur.PolygonBoundaryAmpleParameter

/-!
# The unrestricted closed cyclic locus for actual split polygons

The constructed split m-gon has a closed parameter scheme for full cyclic
orbit subgroups of independently specified rank n. It covers arbitrary cyclic
subgroups on every base change of that polygon, retaining auxiliary sections.
This concerns split polygon families, not a deformation chart for all singular curves.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
open scoped CategoryTheory.Obj
namespace FLT.Mazur.PolygonCyclicBoundary
open PolygonBoundaryModuli CyclicBoundaryParameter GeneralizedEllipticCurve
open GroupSectionBaseChange
open UniversalWeierstrass (Labels)
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (K : Type) [Field K] (m : ℕ) [NeZero m] (n : ℕ) [NeZero n]
local notation "E" => boundaryCurve K m

/-- The full closed multiplication locus on the actual split polygon, of arbitrary cyclic rank. -/
def unrestrictedBoundaryLocus : Scheme := unrestrictedMultiplicationLocus (E) n

/-- The original closed embedding retains both auxiliary factors and every cyclic label. -/
def unrestrictedBoundaryLocusInclusion : unrestrictedBoundaryLocus K m n ⟶
    (parameter (E).group n).left := unrestrictedMultiplicationLocusInclusion (E) n

instance unrestrictedBoundaryLocusInclusion_closed :
    IsClosedImmersion (unrestrictedBoundaryLocusInclusion K m n) :=
  unrestrictedMultiplicationLocusInclusion_closed (E) n

/-- The actual full polygon curve over its closed unrestricted parameter. -/
def unrestrictedBoundaryCurve : GeneralizedEllipticCurve (unrestrictedBoundaryLocus K m n) :=
  unrestrictedLocusCurve (E) n

/-- The finite subgroup on that curve retains the full orbit scheme. -/
def unrestrictedBoundarySubgroup : (unrestrictedBoundaryCurve K m n).FiniteSubgroup n :=
  unrestrictedLocusSubgroup (E) n

/-- The original residue-one section generates the full closed-locus subgroup. -/
theorem unrestrictedBoundarySubgroup_cartier :
    (unrestrictedBoundarySubgroup K m n).IsCartierGenerator (unrestrictedLocusGenerator (E) n) :=
  unrestrictedLocusGenerator_cartier (E) n

/-- Cyclic subgroups on split-polygon tests are covered by this actual closed locus. -/
theorem exists_unrestrictedBoundary_test {T : Scheme} (g : T ⟶ Spec (.of K))
    (H : ((E).baseChange g).FiniteSubgroup n) (hc : H.IsCyclic)
    (a : Labels 4 →* (𝟙_ (Over T) ⟶ ((E).baseChange g).group))
    (b : Labels 3 →* (𝟙_ (Over T) ⟶ ((E).baseChange g).group)) :
    ∃ (U : Scheme) (q : U ⟶ T), Flat q ∧ Surjective q ∧ LocallyOfFinitePresentation q ∧
      ∃ (k : U ⟶ unrestrictedBoundaryLocus K m n)
        (d : FiniteSubgroup.CompatibleIso (H.baseChange q)
          ((unrestrictedBoundarySubgroup K m n).baseChange k)),
        (∀ j, pullSection q (a j) ≫ d.curve.hom.group =
          pullSection k (unrestrictedLocusLabel (E) n (j, 1, 1))) ∧
        (∀ j, pullSection q (b j) ≫ d.curve.hom.group =
          pullSection k (unrestrictedLocusLabel (E) n (1, j, 1))) := by
  obtain ⟨U, q, hf, hs, hl, P, hP, k, d, ha, hb, _⟩ :=
    exists_original_unrestricted_test (E) n g H hc a b
  exact ⟨U, q, hf, hs, hl, k, d, ha, hb⟩

end FLT.Mazur.PolygonCyclicBoundary
