/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveUnrestrictedChartPresentation

/-!
# Relative coverage over the exact original coefficient map

Every original ample cyclic test has an fppf presentation in the locally
finitely presented unrestricted chart of its supplied generalized curve.
The comparison retains the full curve, subgroup, generator and auxiliary
labels, and the parameter lies over the exact original composite base map.
This is relative coverage for a supplied family, not versality for varying curves.
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
  (g : T ⟶ S)
  (H : (E.baseChange g).FiniteSubgroup n) (hc : H.IsCyclic)
  (a : Labels 4 →* (𝟙_ (Over T) ⟶ (E.baseChange g).group))
  (b : Labels 3 →* (𝟙_ (Over T) ⟶ (E.baseChange g).group))

include hc in
/-- Every original cyclic test has an actual fppf presentation in the same closed boundary locus. -/
theorem exists_original_relative_closed_test :
    ∃ (U : Scheme) (q : U ⟶ T), Flat q ∧ Surjective q ∧ LocallyOfFinitePresentation q ∧
      ∃ (P : 𝟙_ (Over U) ⟶ (H.baseChange q).carrier)
        (_ : (H.baseChange q).IsCartierGenerator P)
        (k : U ⟶ unrestrictedMultiplicationLocus E n)
        (d : FiniteSubgroup.CompatibleIso (H.baseChange q)
          ((unrestrictedLocusSubgroup E n).baseChange k)),
        k ≫ unrestrictedLocusBase E n = q ≫ g ∧
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
  refine ⟨U, q, hf, hs, hl, P, hP, k, c.trans d, ?_, ?_, ?_, ?_⟩
  · change k ≫ (unrestrictedMultiplicationLocusInclusion E n ≫ _) = q ≫ g
    rw [← Category.assoc, generatorLocusLift_inclusion]
    exact (generatorParameter E n (q ≫ g) J hJ A B).w
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

variable (ha : H.IsAmple)

include hc ha in
/-- The ample chart covers original tests with every auxiliary label and generator retained. -/
theorem exists_original_relative_ample_test :
    ∃ (U : Scheme) (q : U ⟶ T), Flat q ∧ Surjective q ∧ LocallyOfFinitePresentation q ∧
      ∃ (P : 𝟙_ (Over U) ⟶ (H.baseChange q).carrier)
        (_ : (H.baseChange q).IsCartierGenerator P)
        (v : U ⟶ (unrestrictedAmpleOpen E n).toScheme)
        (d : FiniteSubgroup.CompatibleIso (H.baseChange q)
          ((unrestrictedAmpleLevel E n).val.2.baseChange v)),
        v ≫ unrestrictedAmpleBase E n = q ≫ g ∧
        (∀ j, pullSection q (a j) ≫ d.curve.hom.group =
          pullSection v (unrestrictedAmpleLabel E n (j, 1, 1))) ∧
        (∀ j, pullSection q (b j) ≫ d.curve.hom.group =
          pullSection v (unrestrictedAmpleLabel E n (1, j, 1))) ∧
        P ≫ d.subgroup.hom = pullSection v (unrestrictedAmpleGenerator E n) := by
  obtain ⟨U, q, hf, hs, hl, P, hP, k, d, hk, hA, hB, hG⟩ :=
    exists_original_relative_closed_test E n g H hc a b
  let v := unrestrictedAmpleLift E n (H.baseChange q) k d (ha.baseChange q)
  let e := unrestrictedAmpleLiftSubgroupIso E n (H.baseChange q) k d (ha.baseChange q)
  refine ⟨U, q, hf, hs, hl, P, hP, v, e, ?_, ?_, ?_, ?_⟩
  · change v ≫ ((unrestrictedAmpleOpen E n).ι ≫ unrestrictedLocusBase E n) = q ≫ g
    rw [← Category.assoc, unrestrictedAmpleLift_inclusion]
    exact hk
  · intro j
    exact unrestrictedAmpleLiftSubgroupIso_label E n (H.baseChange q) k d
      (ha.baseChange q) (j, 1, 1) _ (hA j)
  · intro j
    exact unrestrictedAmpleLiftSubgroupIso_label E n (H.baseChange q) k d
      (ha.baseChange q) (1, j, 1) _ (hB j)
  · exact unrestrictedAmpleLiftSubgroupIso_generator E n (H.baseChange q) k d
      (ha.baseChange q) P hG

end FLT.Mazur.CyclicBoundaryParameter
