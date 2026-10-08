/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassAllOrdinaryTripleGlobal
public import FLT.Mazur.WeierstrassOrdinaryTripleDomain

/-!
# Genuine intersections of four ordinary triple charts

Successive pullbacks cut out the actual open locus of the triple product where the
proved ordinary comparison applies. The projections carry the original inputs;
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

/-- Impose the actual left outer ordinary domain. -/
abbrev AllOrdinaryTripleOuterLeft (b c d : Bool) :=
  pullback (ordinaryGlobalDomain W d)
    (ordinaryTripleInnerMap W b c ≫ integralCurveAddFirstPair W hΔ)

/-- The left outer domain retains the same triple. -/
def allOrdinaryTripleOuterLeftMap (b c d : Bool) :
    AllOrdinaryTripleOuterLeft W hΔ b c d ⟶ integralCurveTriple W :=
  pullback.snd _ _ ≫ ordinaryTripleInnerMap W b c

/-- The genuine intersection where both outer additions use ordinary charts. -/
abbrev AllOrdinaryTripleDomain (b c d e : Bool) :=
  pullback (ordinaryGlobalDomain W e)
    (allOrdinaryTripleOuterLeftMap W hΔ b c d ≫ integralCurveAddLastPair W hΔ)

/-- Inclusion of the actual four-domain intersection into the triple product. -/
def allOrdinaryTripleDomainMap (b c d e : Bool) :
    AllOrdinaryTripleDomain W hΔ b c d e ⟶ integralCurveTriple W :=
  pullback.snd _ _ ≫ allOrdinaryTripleOuterLeftMap W hΔ b c d

instance allOrdinaryTripleDomainMap_isOpenImmersion (b c d e : Bool) :
    IsOpenImmersion (allOrdinaryTripleDomainMap W hΔ b c d e) := by
  unfold allOrdinaryTripleDomainMap allOrdinaryTripleOuterLeftMap ordinaryTripleInnerMap
  infer_instance

/-- Projection to the first ordinary inner chart. -/
def allOrdinaryTripleDomainFirst (b c d e : Bool) : AllOrdinaryTripleDomain W hΔ b c d e ⟶
    Spec (additionChartRing W (ordinaryIndex b)) :=
  pullback.snd _ _ ≫ pullback.snd _ _ ≫ pullback.snd _ _ ≫ pullback.fst _ _

/-- Projection to the second ordinary inner chart. -/
def allOrdinaryTripleDomainLast (b c d e : Bool) : AllOrdinaryTripleDomain W hΔ b c d e ⟶
    Spec (additionChartRing W (ordinaryIndex c)) :=
  pullback.snd _ _ ≫ pullback.snd _ _ ≫ pullback.fst _ _

/-- Projection to the left outer ordinary chart. -/
def allOrdinaryTripleDomainLeft (b c d e : Bool) : AllOrdinaryTripleDomain W hΔ b c d e ⟶
    Spec (additionChartRing W (ordinaryIndex d)) :=
  pullback.snd _ _ ≫ pullback.fst _ _

/-- Projection to the right outer ordinary chart. -/
abbrev allOrdinaryTripleDomainRight (b c d e : Bool) : AllOrdinaryTripleDomain W hΔ b c d e ⟶
    Spec (additionChartRing W (ordinaryIndex e)) := pullback.fst _ _

/-- The first chart carries the original first pair. -/
theorem allOrdinaryTripleDomainFirst_inputs (b c d e : Bool) :
    allOrdinaryTripleDomainFirst W hΔ b c d e ≫ ordinaryGlobalDomain W b =
      allOrdinaryTripleDomainMap W hΔ b c d e ≫ integralCurveTriplePair W := by
  simp only [allOrdinaryTripleDomainFirst, allOrdinaryTripleDomainMap,
    allOrdinaryTripleOuterLeftMap,
    ordinaryTripleInnerMap, Category.assoc]
  rw [pullback.condition]

/-- The last chart carries the original last pair. -/
theorem allOrdinaryTripleDomainLast_inputs (b c d e : Bool) :
    allOrdinaryTripleDomainLast W hΔ b c d e ≫ ordinaryGlobalDomain W c =
      allOrdinaryTripleDomainMap W hΔ b c d e ≫ integralCurveTripleLastPair W := by
  simp only [allOrdinaryTripleDomainLast, allOrdinaryTripleDomainMap, allOrdinaryTripleOuterLeftMap,
    ordinaryTripleInnerMap, Category.assoc]
  simp only [pullback.condition]

/-- The left outer chart carries the actual first sum and third input. -/
theorem allOrdinaryTripleDomainLeft_inputs (b c d e : Bool) :
    allOrdinaryTripleDomainLeft W hΔ b c d e ≫ ordinaryGlobalDomain W d =
      allOrdinaryTripleDomainMap W hΔ b c d e ≫ integralCurveAddFirstPair W hΔ := by
  simp only [allOrdinaryTripleDomainLeft, allOrdinaryTripleDomainMap, allOrdinaryTripleOuterLeftMap,
    Category.assoc]
  simp only [pullback.condition]

/-- The right outer chart carries the actual first input and last sum. -/
theorem allOrdinaryTripleDomainRight_inputs (b c d e : Bool) :
    allOrdinaryTripleDomainRight W hΔ b c d e ≫ ordinaryGlobalDomain W e =
      allOrdinaryTripleDomainMap W hΔ b c d e ≫ integralCurveAddLastPair W hΔ := by
  exact pullback.condition.trans (Category.assoc _ _ _).symm

/-- Associativity holds on the genuine four-chart intersection. -/
theorem allOrdinaryTripleDomain_associativity (b c d e : Bool) :
    allOrdinaryTripleDomainMap W hΔ b c d e ≫ integralCurveTripleAddLeft W hΔ =
      allOrdinaryTripleDomainMap W hΔ b c d e ≫ integralCurveTripleAddRight W hΔ :=
  integralCurveTripleAdd_allOrdinary W hΔ (allOrdinaryTripleDomainMap W hΔ b c d e) b c d e
    (allOrdinaryTripleDomainFirst W hΔ b c d e) (allOrdinaryTripleDomainLast W hΔ b c d e)
    (allOrdinaryTripleDomainLeft W hΔ b c d e) (allOrdinaryTripleDomainRight W hΔ b c d e)
    (allOrdinaryTripleDomainFirst_inputs W hΔ b c d e)
    (allOrdinaryTripleDomainLast_inputs W hΔ b c d e)
    (allOrdinaryTripleDomainLeft_inputs W hΔ b c d e)
    (allOrdinaryTripleDomainRight_inputs W hΔ b c d e)

end FLT.Mazur.WeierstrassIntegralChart
