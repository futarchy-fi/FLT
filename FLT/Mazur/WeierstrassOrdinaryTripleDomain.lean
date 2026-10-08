/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassOrdinaryTripleGlobalComparison

/-!
# Genuine ordinary-inner and secant-outer triple intersections

Four pullbacks cut out the actual open locus of the triple product where the
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

/-- First ordinary inner domain, pulled back to the true triple product. -/
abbrev OrdinaryTripleFirst (b : Bool) :=
  pullback (ordinaryGlobalDomain W b) (integralCurveTriplePair W)

/-- Its original triple input. -/
abbrev ordinaryTripleFirstMap (b : Bool) : OrdinaryTripleFirst W b ⟶ integralCurveTriple W :=
  pullback.snd _ _

/-- Impose the second ordinary inner domain on the first. -/
abbrev OrdinaryTripleInner (b c : Bool) :=
  pullback (ordinaryGlobalDomain W c)
    (ordinaryTripleFirstMap W b ≫ integralCurveTripleLastPair W)

/-- The common inner domain retains its original triple input. -/
def ordinaryTripleInnerMap (b c : Bool) : OrdinaryTripleInner W b c ⟶ integralCurveTriple W :=
  pullback.snd _ _ ≫ ordinaryTripleFirstMap W b

variable (hΔ : IsUnit W.Δ)

/-- Impose the actual left outer secant domain. -/
abbrev OrdinaryTripleOuterLeft (b c : Bool) :=
  pullback (ordinaryGlobalDomain W false)
    (ordinaryTripleInnerMap W b c ≫ integralCurveAddFirstPair W hΔ)

/-- The left outer domain retains the same triple. -/
def ordinaryTripleOuterLeftMap (b c : Bool) :
    OrdinaryTripleOuterLeft W hΔ b c ⟶ integralCurveTriple W :=
  pullback.snd _ _ ≫ ordinaryTripleInnerMap W b c

/-- The genuine intersection where both outer additions use secant charts. -/
abbrev OrdinaryTripleDomain (b c : Bool) :=
  pullback (ordinaryGlobalDomain W false)
    (ordinaryTripleOuterLeftMap W hΔ b c ≫ integralCurveAddLastPair W hΔ)

/-- Inclusion of the actual four-domain intersection into the triple product. -/
def ordinaryTripleDomainMap (b c : Bool) :
    OrdinaryTripleDomain W hΔ b c ⟶ integralCurveTriple W :=
  pullback.snd _ _ ≫ ordinaryTripleOuterLeftMap W hΔ b c

instance ordinaryTripleDomainMap_isOpenImmersion (b c : Bool) :
    IsOpenImmersion (ordinaryTripleDomainMap W hΔ b c) := by
  unfold ordinaryTripleDomainMap ordinaryTripleOuterLeftMap ordinaryTripleInnerMap
  infer_instance

/-- Projection to the first ordinary inner chart. -/
def ordinaryTripleDomainFirst (b c : Bool) : OrdinaryTripleDomain W hΔ b c ⟶
    Spec (additionChartRing W (ordinaryIndex b)) :=
  pullback.snd _ _ ≫ pullback.snd _ _ ≫ pullback.snd _ _ ≫ pullback.fst _ _

/-- Projection to the second ordinary inner chart. -/
def ordinaryTripleDomainLast (b c : Bool) : OrdinaryTripleDomain W hΔ b c ⟶
    Spec (additionChartRing W (ordinaryIndex c)) :=
  pullback.snd _ _ ≫ pullback.snd _ _ ≫ pullback.fst _ _

/-- Projection to the left outer secant chart. -/
def ordinaryTripleDomainLeft (b c : Bool) : OrdinaryTripleDomain W hΔ b c ⟶
    Spec (additionChartRing W (ordinaryIndex false)) :=
  pullback.snd _ _ ≫ pullback.fst _ _

/-- Projection to the right outer secant chart. -/
abbrev ordinaryTripleDomainRight (b c : Bool) : OrdinaryTripleDomain W hΔ b c ⟶
    Spec (additionChartRing W (ordinaryIndex false)) := pullback.fst _ _

/-- The first chart carries the original first pair. -/
theorem ordinaryTripleDomainFirst_inputs (b c : Bool) :
    ordinaryTripleDomainFirst W hΔ b c ≫ ordinaryGlobalDomain W b =
      ordinaryTripleDomainMap W hΔ b c ≫ integralCurveTriplePair W := by
  simp only [ordinaryTripleDomainFirst, ordinaryTripleDomainMap, ordinaryTripleOuterLeftMap,
    ordinaryTripleInnerMap, Category.assoc]
  rw [pullback.condition]

/-- The last chart carries the original last pair. -/
theorem ordinaryTripleDomainLast_inputs (b c : Bool) :
    ordinaryTripleDomainLast W hΔ b c ≫ ordinaryGlobalDomain W c =
      ordinaryTripleDomainMap W hΔ b c ≫ integralCurveTripleLastPair W := by
  simp only [ordinaryTripleDomainLast, ordinaryTripleDomainMap, ordinaryTripleOuterLeftMap,
    ordinaryTripleInnerMap, Category.assoc]
  simp only [pullback.condition]

/-- The left outer chart carries the actual first sum and third input. -/
theorem ordinaryTripleDomainLeft_inputs (b c : Bool) :
    ordinaryTripleDomainLeft W hΔ b c ≫ ordinaryGlobalDomain W false =
      ordinaryTripleDomainMap W hΔ b c ≫ integralCurveAddFirstPair W hΔ := by
  simp only [ordinaryTripleDomainLeft, ordinaryTripleDomainMap, ordinaryTripleOuterLeftMap,
    Category.assoc]
  simp only [pullback.condition]

/-- The right outer chart carries the actual first input and last sum. -/
theorem ordinaryTripleDomainRight_inputs (b c : Bool) :
    ordinaryTripleDomainRight W hΔ b c ≫ ordinaryGlobalDomain W false =
      ordinaryTripleDomainMap W hΔ b c ≫ integralCurveAddLastPair W hΔ := by
  exact pullback.condition.trans (Category.assoc _ _ _).symm

/-- Associativity holds on the genuine four-chart intersection. -/
theorem ordinaryTripleDomain_associativity (b c : Bool) :
    ordinaryTripleDomainMap W hΔ b c ≫ integralCurveTripleAddLeft W hΔ =
      ordinaryTripleDomainMap W hΔ b c ≫ integralCurveTripleAddRight W hΔ :=
  integralCurveTripleAdd_ordinarySecant W hΔ (ordinaryTripleDomainMap W hΔ b c) b c
    (ordinaryTripleDomainFirst W hΔ b c) (ordinaryTripleDomainLast W hΔ b c)
    (ordinaryTripleDomainLeft W hΔ b c) (ordinaryTripleDomainRight W hΔ b c)
    (ordinaryTripleDomainFirst_inputs W hΔ b c) (ordinaryTripleDomainLast_inputs W hΔ b c)
    (ordinaryTripleDomainLeft_inputs W hΔ b c) (ordinaryTripleDomainRight_inputs W hΔ b c)

end FLT.Mazur.WeierstrassIntegralChart
