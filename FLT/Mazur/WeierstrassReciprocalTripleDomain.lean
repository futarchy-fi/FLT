/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassReciprocalTripleGlobal
public import FLT.Mazur.WeierstrassOrdinaryTripleDomain

/-!
# Genuine reciprocal outer triple intersections

Successive pullbacks cut out the actual open locus of the triple product where the
proved reciprocal comparison applies. The projections carry the original inputs;
associativity on this locus needs no supplied compatibility or output equality.
This locus is not asserted to cover the triple product.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

variable (hΔ : IsUnit W.Δ)

/-- Impose the actual left outer reciprocal domain. -/
abbrev RecipTripleOuterLeft (b c d : Bool) :=
  pullback (reciprocalGlobalDomain W d)
    (ordinaryTripleInnerMap W b c ≫ integralCurveAddFirstPair W hΔ)

/-- The left outer domain retains the same triple. -/
def recipTripleOuterLeftMap (b c d : Bool) :
    RecipTripleOuterLeft W hΔ b c d ⟶ integralCurveTriple W :=
  pullback.snd _ _ ≫ ordinaryTripleInnerMap W b c

/-- The genuine intersection where both outer additions use reciprocals. -/
abbrev RecipTripleDomain (b c d e : Bool) :=
  pullback (reciprocalGlobalDomain W e)
    (recipTripleOuterLeftMap W hΔ b c d ≫ integralCurveAddLastPair W hΔ)

/-- Inclusion of the actual four-domain intersection into the triple product. -/
def recipTripleDomainMap (b c d e : Bool) :
    RecipTripleDomain W hΔ b c d e ⟶ integralCurveTriple W :=
  pullback.snd _ _ ≫ recipTripleOuterLeftMap W hΔ b c d

instance recipTripleDomainMap_isOpenImmersion (b c d e : Bool) :
    IsOpenImmersion (recipTripleDomainMap W hΔ b c d e) := by
  unfold recipTripleDomainMap recipTripleOuterLeftMap ordinaryTripleInnerMap
  infer_instance

/-- Projection to the first ordinary inner chart. -/
def recipTripleDomainFirst (b c d e : Bool) : RecipTripleDomain W hΔ b c d e ⟶
    Spec (additionChartRing W (ordinaryIndex b)) :=
  pullback.snd _ _ ≫ pullback.snd _ _ ≫ pullback.snd _ _ ≫ pullback.fst _ _

/-- Projection to the second ordinary inner chart. -/
def recipTripleDomainLast (b c d e : Bool) : RecipTripleDomain W hΔ b c d e ⟶
    Spec (additionChartRing W (ordinaryIndex c)) :=
  pullback.snd _ _ ≫ pullback.snd _ _ ≫ pullback.fst _ _

/-- Projection to the left outer reciprocal chart. -/
def recipTripleDomainLeft (b c d e : Bool) : RecipTripleDomain W hΔ b c d e ⟶
    Spec (additionChartRing W (reciprocalIndex d)) :=
  pullback.snd _ _ ≫ pullback.fst _ _

/-- Projection to the right outer reciprocal chart. -/
abbrev recipTripleDomainRight (b c d e : Bool) : RecipTripleDomain W hΔ b c d e ⟶
    Spec (additionChartRing W (reciprocalIndex e)) := pullback.fst _ _

/-- The first chart carries the original first pair. -/
theorem recipTripleDomainFirst_inputs (b c d e : Bool) :
    recipTripleDomainFirst W hΔ b c d e ≫ ordinaryGlobalDomain W b =
      recipTripleDomainMap W hΔ b c d e ≫ integralCurveTriplePair W := by
  simp only [recipTripleDomainFirst, recipTripleDomainMap,
    recipTripleOuterLeftMap,
    ordinaryTripleInnerMap, Category.assoc]
  rw [pullback.condition]

/-- The last chart carries the original last pair. -/
theorem recipTripleDomainLast_inputs (b c d e : Bool) :
    recipTripleDomainLast W hΔ b c d e ≫ ordinaryGlobalDomain W c =
      recipTripleDomainMap W hΔ b c d e ≫ integralCurveTripleLastPair W := by
  simp only [recipTripleDomainLast, recipTripleDomainMap, recipTripleOuterLeftMap,
    ordinaryTripleInnerMap, Category.assoc]
  simp only [pullback.condition]

/-- The left outer chart carries the actual first sum and third input. -/
theorem recipTripleDomainLeft_inputs (b c d e : Bool) :
    recipTripleDomainLeft W hΔ b c d e ≫ reciprocalGlobalDomain W d =
      recipTripleDomainMap W hΔ b c d e ≫ integralCurveAddFirstPair W hΔ := by
  simp only [recipTripleDomainLeft, recipTripleDomainMap, recipTripleOuterLeftMap,
    Category.assoc]
  simp only [pullback.condition]

/-- The right outer chart carries the actual first input and last sum. -/
theorem recipTripleDomainRight_inputs (b c d e : Bool) :
    recipTripleDomainRight W hΔ b c d e ≫ reciprocalGlobalDomain W e =
      recipTripleDomainMap W hΔ b c d e ≫ integralCurveAddLastPair W hΔ := by
  exact pullback.condition.trans (Category.assoc _ _ _).symm

/-- Associativity holds on the genuine four-chart intersection. -/
theorem recipTripleDomain_associativity (b c d e : Bool) :
    recipTripleDomainMap W hΔ b c d e ≫ integralCurveTripleAddLeft W hΔ =
      recipTripleDomainMap W hΔ b c d e ≫ integralCurveTripleAddRight W hΔ :=
  integralCurveTripleAdd_reciprocals W hΔ (recipTripleDomainMap W hΔ b c d e) b c d e
    (recipTripleDomainFirst W hΔ b c d e) (recipTripleDomainLast W hΔ b c d e)
    (recipTripleDomainLeft W hΔ b c d e) (recipTripleDomainRight W hΔ b c d e)
    (recipTripleDomainFirst_inputs W hΔ b c d e)
    (recipTripleDomainLast_inputs W hΔ b c d e)
    (recipTripleDomainLeft_inputs W hΔ b c d e)
    (recipTripleDomainRight_inputs W hΔ b c d e)

end FLT.Mazur.WeierstrassIntegralChart
