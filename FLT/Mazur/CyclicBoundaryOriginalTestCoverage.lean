/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicBoundaryGeneratorCoverage
public import FLT.Mazur.CompatibleSubgroupAuxiliaryTransport

/-!
# Unrestricted coverage on arbitrary original tests

The generator cover of a subgroup on an arbitrary base change gives tests
of the same original boundary parameter scheme. Flattening the base change
retains the full curve, subgroup, generator and both auxiliary markings.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
open scoped CategoryTheory.Obj
namespace FLT.Mazur.CyclicBoundaryParameter
open GeneralizedEllipticCurve GroupSectionBaseChange
open UniversalWeierstrass (Labels)
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S T : Scheme} (E : GeneralizedEllipticCurve S) (n : ℕ) [NeZero n]
  [SmoothOfRelativeDimension 1 E.group.hom] (g : T ⟶ S)
  (H : (E.baseChange g).FiniteSubgroup n) (hc : H.IsCyclic)
  (a : Labels 4 →* (𝟙_ (Over T) ⟶ (E.baseChange g).group))
  (b : Labels 3 →* (𝟙_ (Over T) ⟶ (E.baseChange g).group))

include hc in
/-- Every original cyclic test has an actual fppf presentation in the same closed boundary locus. -/
theorem exists_original_unrestricted_test :
    ∃ (U : Scheme) (q : U ⟶ T), Flat q ∧ Surjective q ∧ LocallyOfFinitePresentation q ∧
      ∃ (P : 𝟙_ (Over U) ⟶ (H.baseChange q).carrier)
        (_ : (H.baseChange q).IsCartierGenerator P)
        (k : U ⟶ unrestrictedMultiplicationLocus E n)
        (d : FiniteSubgroup.CompatibleIso (H.baseChange q)
          ((unrestrictedLocusSubgroup E n).baseChange k)),
        (∀ j, pullSection q (a j) ≫ d.curve.hom.group =
          pullSection k (unrestrictedLocusLabel E n (j, 1, 1))) ∧
        (∀ j, pullSection q (b j) ≫ d.curve.hom.group =
          pullSection k (unrestrictedLocusLabel E n (1, j, 1))) ∧
        P ≫ d.subgroup.hom = pullSection k (unrestrictedLocusGenerator E n) := by
  obtain ⟨U, q, hf, hs, hl, P, hP⟩ := hc
  let e := (E.baseChangeCompIso g q).symm
  let J := (H.baseChange q).transport e
  let c := (H.baseChange q).transportCompatibleIso e
  have hJ : J.IsCartierGenerator P := (H.baseChange q).transport_cartierGenerator e hP
  let A := c.transportAuxiliary (pullMarking q (E.baseChange g) a)
  let B := c.transportAuxiliary (pullMarking q (E.baseChange g) b)
  let k := generatorLocusLift E n (q ≫ g) J hJ A B
  let d := generatorLocusSubgroupIso E n (q ≫ g) J hJ A B
  refine ⟨U, q, hf, hs, hl, P, hP, k, c.trans d, ?_, ?_, ?_⟩
  · intro j
    change pullSection q (a j) ≫ (c.curve.hom.group ≫ d.curve.hom.group) = _
    rw [← Category.assoc]
    exact generatorLocusSubgroupIso_four E n (q ≫ g) J hJ A B j
  · intro j
    change pullSection q (b j) ≫ (c.curve.hom.group ≫ d.curve.hom.group) = _
    rw [← Category.assoc]
    exact generatorLocusSubgroupIso_three E n (q ≫ g) J hJ A B j
  · change P ≫ (𝟙 _ ≫ d.subgroup.hom) = _
    rw [Category.id_comp]
    exact generatorLocusSubgroupIso_generator E n (q ≫ g) J hJ A B

end FLT.Mazur.CyclicBoundaryParameter
