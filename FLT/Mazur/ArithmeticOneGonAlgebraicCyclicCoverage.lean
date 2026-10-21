/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ArithmeticOneGonAlgebraicCyclicCharts

/-!
# Cyclic coverage while the arithmetic degeneration parameter varies

Every original cyclic subgroup on an arithmetic one-gon is fppf locally a
pullback from the fixed integral chart. The full generalized curve comparison
retains its action, both auxiliary markings, and the original Cartier generator.
This covers this explicit varying family, not all generalized curves.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
open scoped CategoryTheory.Obj
namespace FLT.Mazur.ArithmeticOneGonParameter
open GeneralizedEllipticCurve GroupSectionBaseChange CyclicBoundaryParameter
open ArithmeticOneGonGeneralizedCurve
open UniversalWeierstrass (Labels)
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] (t : R) (ht : IsUnit (1 + 432 * t))
  (n : ℕ) [NeZero n] (H : (curve t ht).FiniteSubgroup n) (hc : H.IsCyclic)
  (a : Labels 4 →* (𝟙_ (Over (Spec (.of R))) ⟶ (curve t ht).group))
  (b : Labels 3 →* (𝟙_ (Over (Spec (.of R))) ⟶ (curve t ht).group))

include hc in
/-- Every original cyclic test has an actual fppf presentation in the same closed boundary locus. -/
theorem exists_arithmetic_closed_test :
    ∃ (U : Scheme) (q : U ⟶ Spec (.of R)), Flat q ∧ Surjective q ∧ LocallyOfFinitePresentation q ∧
      ∃ (P : 𝟙_ (Over U) ⟶ (H.baseChange q).carrier)
        (_ : (H.baseChange q).IsCartierGenerator P)
        (k : U ⟶ unrestrictedMultiplicationLocus universalCurve n)
        (d : FiniteSubgroup.CompatibleIso (H.baseChange q)
          ((unrestrictedLocusSubgroup universalCurve n).baseChange k)),
        k ≫ unrestrictedLocusBase universalCurve n = q ≫ parameterMap t ht ∧
        (∀ j, pullSection q (a j) ≫ d.curve.hom.group =
          pullSection k (unrestrictedLocusLabel universalCurve n (j, 1, 1))) ∧
        (∀ j, pullSection q (b j) ≫ d.curve.hom.group =
          pullSection k (unrestrictedLocusLabel universalCurve n (1, j, 1))) ∧
        P ≫ d.subgroup.hom = pullSection k (unrestrictedLocusGenerator universalCurve n) := by
  obtain ⟨U, q, hf, hs, hl, P, hP⟩ := hc
  let e := (baseChangeFunctor q).mapIso (specializationIso t ht) ≪≫
    (universalCurve.baseChangeCompIso (parameterMap t ht) q).symm
  let J := (H.baseChange q).transport e
  let c := (H.baseChange q).transportCompatibleIso e
  have hJ : J.IsCartierGenerator P := (H.baseChange q).transport_cartierGenerator e hP
  let A := c.transportAuxiliary (pullMarking q (curve t ht) a)
  let B := c.transportAuxiliary (pullMarking q (curve t ht) b)
  let k := generatorLocusLift universalCurve n (q ≫ parameterMap t ht) J hJ A B
  let d := generatorLocusSubgroupIso universalCurve n (q ≫ parameterMap t ht) J hJ A B
  refine ⟨U, q, hf, hs, hl, P, hP, k, c.trans d, ?_, ?_, ?_, ?_⟩
  · change k ≫ (unrestrictedMultiplicationLocusInclusion universalCurve n ≫ _) =
        q ≫ parameterMap t ht
    rw [← Category.assoc, generatorLocusLift_inclusion]
    exact (generatorParameter universalCurve n (q ≫ parameterMap t ht) J hJ A B).w
  · intro j
    change pullSection q (a j) ≫ (c.curve.hom.group ≫ d.curve.hom.group) = _
    rw [← Category.assoc]
    exact generatorLocusSubgroupIso_four universalCurve n (q ≫ parameterMap t ht) J hJ A B j
  · intro j
    change pullSection q (b j) ≫ (c.curve.hom.group ≫ d.curve.hom.group) = _
    rw [← Category.assoc]
    exact generatorLocusSubgroupIso_three universalCurve n (q ≫ parameterMap t ht) J hJ A B j
  · change P ≫ (𝟙 _ ≫ d.subgroup.hom) = _
    rw [Category.id_comp]
    exact generatorLocusSubgroupIso_generator universalCurve n (q ≫ parameterMap t ht) J hJ A B

variable (ha : H.IsAmple)

include hc ha in
/-- The ample chart covers original tests with every auxiliary label and generator retained. -/
theorem exists_arithmetic_ample_test :
    ∃ (U : Scheme) (q : U ⟶ Spec (.of R)), Flat q ∧ Surjective q ∧ LocallyOfFinitePresentation q ∧
      ∃ (P : 𝟙_ (Over U) ⟶ (H.baseChange q).carrier)
        (_ : (H.baseChange q).IsCartierGenerator P)
        (v : U ⟶ (unrestrictedAmpleOpen universalCurve n).toScheme)
        (d : FiniteSubgroup.CompatibleIso (H.baseChange q)
          ((unrestrictedAmpleLevel universalCurve n).val.2.baseChange v)),
        v ≫ unrestrictedAmpleBase universalCurve n = q ≫ parameterMap t ht ∧
        (∀ j, pullSection q (a j) ≫ d.curve.hom.group =
          pullSection v (unrestrictedAmpleLabel universalCurve n (j, 1, 1))) ∧
        (∀ j, pullSection q (b j) ≫ d.curve.hom.group =
          pullSection v (unrestrictedAmpleLabel universalCurve n (1, j, 1))) ∧
        P ≫ d.subgroup.hom = pullSection v (unrestrictedAmpleGenerator universalCurve n) := by
  obtain ⟨U, q, hf, hs, hl, P, hP, k, d, hk, hA, hB, hG⟩ :=
    exists_arithmetic_closed_test t ht n H hc a b
  let v := unrestrictedAmpleLift universalCurve n (H.baseChange q) k d (ha.baseChange q)
  let e := unrestrictedAmpleLiftSubgroupIso universalCurve n (H.baseChange q) k d (ha.baseChange q)
  refine ⟨U, q, hf, hs, hl, P, hP, v, e, ?_, ?_, ?_, ?_⟩
  · change v ≫ ((unrestrictedAmpleOpen universalCurve n).ι ≫
        unrestrictedLocusBase universalCurve n) =
        q ≫ parameterMap t ht
    rw [← Category.assoc, unrestrictedAmpleLift_inclusion]
    exact hk
  · intro j
    exact unrestrictedAmpleLiftSubgroupIso_label universalCurve n (H.baseChange q) k d
      (ha.baseChange q) (j, 1, 1) _ (hA j)
  · intro j
    exact unrestrictedAmpleLiftSubgroupIso_label universalCurve n (H.baseChange q) k d
      (ha.baseChange q) (1, j, 1) _ (hB j)
  · exact unrestrictedAmpleLiftSubgroupIso_generator universalCurve n (H.baseChange q) k d
      (ha.baseChange q) P hG

end FLT.Mazur.ArithmeticOneGonParameter
