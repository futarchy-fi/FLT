/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveSubgroupIdeal
public import FLT.Mazur.GroupSectionBaseChange

/-!
# Cartier generators of finite subgroups

A generator is a torsion section whose powers sum scheme-theoretically to
the actual relative Cartier subgroup divisor. Multiplicities are retained.
Arbitrary base change preserves this condition, including nonreduced bases.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory MonObj
open scoped CategoryTheory.Obj
namespace FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
variable {S T : Scheme} {E : GeneralizedEllipticCurve S} {n : ℕ}
  (H : E.FiniteSubgroup n)

/-- A Cartier generator, using the powers of an actual subgroup section. -/
def IsCartierGenerator (P : 𝟙_ (Over S) ⟶ H.carrier) : Prop :=
  P ^ n = 1 ∧ FCurve.RelativeEffectiveCartier E.curve.hom H.ideal ∧
    H.ideal = ∏ i : Fin n, ((P ^ i.val) ≫ H.curveMap).left.ker

/-- The generator section on the actual pulled-back subgroup. -/
def pullGenerator (g : T ⟶ S) (P : 𝟙_ (Over S) ⟶ H.carrier) :
    𝟙_ (Over T) ⟶ (H.baseChange g).carrier := GroupSectionBaseChange.pullSection g P

/-- The pulled-back generator orbit agrees with the pullback of each orbit section. -/
theorem pullGenerator_orbit (g : T ⟶ S) (P : 𝟙_ (Over S) ⟶ H.carrier) (i : ℕ) :
    (H.pullGenerator g P ^ i) ≫ (H.baseChange g).curveMap =
      GroupSectionBaseChange.pullSection g ((P ^ i) ≫ H.curveMap) := by
  rw [baseChange_curveMap, GroupSectionBaseChange.section_comp,
    GroupSectionBaseChange.section_pow]
  rfl

/-- A Cartier generator remains a Cartier generator after arbitrary base change. -/
theorem IsCartierGenerator.baseChange {P : 𝟙_ (Over S) ⟶ H.carrier}
    (hP : H.IsCartierGenerator P) (g : T ⟶ S) :
    (H.baseChange g).IsCartierGenerator (H.pullGenerator g P) := by
  have : IsProper E.curve.hom := E.family.family.1
  refine ⟨?_, ?_, ?_⟩
  · change GroupSectionBaseChange.pullSection g P ^ n = 1
    rw [← GroupSectionBaseChange.section_pow, hP.1]
    simp [GroupSectionBaseChange.pullSection, Functor.map_one]
  · rw [baseChange_ideal]
    exact FCurve.relativeCartierBaseChange E.curve.hom g H.ideal hP.2.1
  · rw [baseChange_ideal, hP.2.2, FCurve.idealSheaf_comap_prod]
    apply Finset.prod_congr rfl
    intro i _
    rw [pullGenerator_orbit, GroupSectionBaseChange.section_ker]

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
