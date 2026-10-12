/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveCyclicMarkingBaseChange
public import FLT.Mazur.CartierGeneratorMarkedSubgroup
public import FLT.Mazur.SectionSumRank

/-!
# Multiplicity-preserving divisors of cyclic markings

The product contains one factor for every cyclic label, also when labels
coincide. On a smooth proper curve it is finite locally free of rank n.
For a Cartier generator it is precisely the original closed subgroup ideal.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S T : Scheme} (E : GeneralizedEllipticCurve S) {n : ℕ}
  (φ : Multiplicative (ZMod n) →* (𝟙_ (Over S) ⟶ E.group))

/-- The whole-curve orbit ideal, retaining a factor for every label. -/
def cyclicMarkingIdeal : E.curve.left.IdealSheafData :=
  ∏ i : Fin n, ((φ (Multiplicative.ofAdd (i.val : ZMod n))) ≫ E.inclusion).left.ker

/-- Every base change retains the actual product ideal, including its multiplicities. -/
theorem cyclicMarkingIdeal_baseChange (g : T ⟶ S) :
    (E.baseChange g).cyclicMarkingIdeal (pullCyclicMarking (E := E) g φ) =
      (E.cyclicMarkingIdeal φ).comap (pullback.fst E.curve.hom g) := by
  have : IsProper E.curve.hom := E.family.family.1
  unfold cyclicMarkingIdeal
  rw [FCurve.idealSheaf_comap_prod]
  apply Finset.prod_congr rfl
  intro i _
  have h := GroupSectionBaseChange.section_ker g
    (φ (.ofAdd (i.val : ZMod n)) ≫ E.inclusion)
  rw [GroupSectionBaseChange.section_comp] at h
  rw [baseChange_inclusion]
  change (GroupSectionBaseChange.pullSection g (φ (.ofAdd (i.val : ZMod n))) ≫
    (Over.pullback g).map E.inclusion).left.ker = _
  exact h

/-- On a smooth whole curve the orbit product is a relative effective Cartier divisor. -/
theorem cyclicMarkingIdeal_cartier [SmoothOfRelativeDimension 1 E.curve.hom] :
    FCurve.RelativeEffectiveCartier E.curve.hom (E.cyclicMarkingIdeal φ) := by
  have : IsProper E.curve.hom := E.family.family.1
  exact FCurve.relativeEffectiveCartier_section_prod E.curve.hom Finset.univ
    (fun i : Fin n ↦ ((φ (.ofAdd (i.val : ZMod n))) ≫ E.inclusion).left)
    (fun i _ ↦ Over.w _)

/-- Collisions do not change the finite locally free rank of the orbit divisor. -/
theorem cyclicMarkingIdeal_degree [SmoothOfRelativeDimension 1 E.curve.hom] :
    FCurve.FiniteLocallyFreeDegree
      ((E.cyclicMarkingIdeal φ).subschemeι ≫ E.curve.hom) n := by
  have : IsProper E.curve.hom := E.family.family.1
  simpa only [cyclicMarkingIdeal, Finset.card_univ, Fintype.card_fin] using
    FCurve.finiteLocallyFreeDegree_section_prod E.curve.hom Finset.univ
      (fun i : Fin n ↦ ((φ (.ofAdd (i.val : ZMod n))) ≫ E.inclusion).left)
      (fun i ↦ Over.w _)

variable [NeZero n] (H : E.FiniteSubgroup n) {P : 𝟙_ (Over S) ⟶ H.carrier}

/-- The generator's orbit divisor is the original subgroup as a closed subscheme. -/
theorem FiniteSubgroup.generatorCurveMarking_ideal (hP : H.IsCartierGenerator P) :
    E.cyclicMarkingIdeal (H.generatorCurveMarking hP) = H.ideal := by
  rw [cyclicMarkingIdeal, hP.2.2]
  apply Finset.prod_congr rfl
  intro i _
  change ((H.generatorPowers P hP.1 (.ofAdd (i.val : ZMod n)) ≫ H.inclusion) ≫
    E.inclusion).left.ker = _
  rw [FiniteSubgroup.generatorPowers_natCast, Category.assoc]
  rfl

end FLT.Mazur.GeneralizedEllipticCurve
