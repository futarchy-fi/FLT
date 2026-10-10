/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassReciprocalSecantTripleGlobal
public import FLT.Mazur.WeierstrassOrdinaryTripleDomain

/-!
# Genuine reciprocal outer secant triple intersections

Successive pullbacks cut out the actual open locus of the triple product where the
proved reciprocal secant comparison applies. The projections carry the original inputs;
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

/-- Impose the actual left outer reciprocal secant domain. -/
abbrev RecipSecantTripleOuterLeft (b c : Bool) :=
  pullback (reciprocalGlobalDomain W false)
    (ordinaryTripleInnerMap W b c ≫ integralCurveAddFirstPair W hΔ)

/-- The left outer domain retains the same triple. -/
def recipSecantTripleOuterLeftMap (b c : Bool) :
    RecipSecantTripleOuterLeft W hΔ b c ⟶ integralCurveTriple W :=
  pullback.snd _ _ ≫ ordinaryTripleInnerMap W b c

/-- The genuine intersection where both outer additions use reciprocal secants. -/
abbrev RecipSecantTripleDomain (b c : Bool) :=
  pullback (reciprocalGlobalDomain W false)
    (recipSecantTripleOuterLeftMap W hΔ b c ≫ integralCurveAddLastPair W hΔ)

/-- Inclusion of the actual four-domain intersection into the triple product. -/
def recipSecantTripleDomainMap (b c : Bool) :
    RecipSecantTripleDomain W hΔ b c ⟶ integralCurveTriple W :=
  pullback.snd _ _ ≫ recipSecantTripleOuterLeftMap W hΔ b c

instance recipSecantTripleDomainMap_isOpenImmersion (b c : Bool) :
    IsOpenImmersion (recipSecantTripleDomainMap W hΔ b c) := by
  unfold recipSecantTripleDomainMap recipSecantTripleOuterLeftMap ordinaryTripleInnerMap
  infer_instance

/-- Projection to the first ordinary inner chart. -/
def recipSecantTripleDomainFirst (b c : Bool) : RecipSecantTripleDomain W hΔ b c ⟶
    Spec (additionChartRing W (ordinaryIndex b)) :=
  pullback.snd _ _ ≫ pullback.snd _ _ ≫ pullback.snd _ _ ≫ pullback.fst _ _

/-- Projection to the second ordinary inner chart. -/
def recipSecantTripleDomainLast (b c : Bool) : RecipSecantTripleDomain W hΔ b c ⟶
    Spec (additionChartRing W (ordinaryIndex c)) :=
  pullback.snd _ _ ≫ pullback.snd _ _ ≫ pullback.fst _ _

/-- Projection to the left outer reciprocal secant chart. -/
def recipSecantTripleDomainLeft (b c : Bool) : RecipSecantTripleDomain W hΔ b c ⟶
    Spec (additionChartRing W (reciprocalIndex false)) :=
  pullback.snd _ _ ≫ pullback.fst _ _

/-- Projection to the right outer reciprocal secant chart. -/
abbrev recipSecantTripleDomainRight (b c : Bool) : RecipSecantTripleDomain W hΔ b c ⟶
    Spec (additionChartRing W (reciprocalIndex false)) := pullback.fst _ _

/-- The first chart carries the original first pair. -/
theorem recipSecantTripleDomainFirst_inputs (b c : Bool) :
    recipSecantTripleDomainFirst W hΔ b c ≫ ordinaryGlobalDomain W b =
      recipSecantTripleDomainMap W hΔ b c ≫ integralCurveTriplePair W := by
  simp only [recipSecantTripleDomainFirst, recipSecantTripleDomainMap,
    recipSecantTripleOuterLeftMap,
    ordinaryTripleInnerMap, Category.assoc]
  rw [pullback.condition]

/-- The last chart carries the original last pair. -/
theorem recipSecantTripleDomainLast_inputs (b c : Bool) :
    recipSecantTripleDomainLast W hΔ b c ≫ ordinaryGlobalDomain W c =
      recipSecantTripleDomainMap W hΔ b c ≫ integralCurveTripleLastPair W := by
  simp only [recipSecantTripleDomainLast, recipSecantTripleDomainMap, recipSecantTripleOuterLeftMap,
    ordinaryTripleInnerMap, Category.assoc]
  simp only [pullback.condition]

/-- The left outer chart carries the actual first sum and third input. -/
theorem recipSecantTripleDomainLeft_inputs (b c : Bool) :
    recipSecantTripleDomainLeft W hΔ b c ≫ reciprocalGlobalDomain W false =
      recipSecantTripleDomainMap W hΔ b c ≫ integralCurveAddFirstPair W hΔ := by
  simp only [recipSecantTripleDomainLeft, recipSecantTripleDomainMap, recipSecantTripleOuterLeftMap,
    Category.assoc]
  simp only [pullback.condition]

/-- The right outer chart carries the actual first input and last sum. -/
theorem recipSecantTripleDomainRight_inputs (b c : Bool) :
    recipSecantTripleDomainRight W hΔ b c ≫ reciprocalGlobalDomain W false =
      recipSecantTripleDomainMap W hΔ b c ≫ integralCurveAddLastPair W hΔ := by
  exact pullback.condition.trans (Category.assoc _ _ _).symm

/-- Associativity holds on the genuine four-chart intersection. -/
theorem recipSecantTripleDomain_associativity (b c : Bool) :
    recipSecantTripleDomainMap W hΔ b c ≫ integralCurveTripleAddLeft W hΔ =
      recipSecantTripleDomainMap W hΔ b c ≫ integralCurveTripleAddRight W hΔ :=
  integralCurveTripleAdd_reciprocalSecants W hΔ (recipSecantTripleDomainMap W hΔ b c) b c
    (recipSecantTripleDomainFirst W hΔ b c) (recipSecantTripleDomainLast W hΔ b c)
    (recipSecantTripleDomainLeft W hΔ b c) (recipSecantTripleDomainRight W hΔ b c)
    (recipSecantTripleDomainFirst_inputs W hΔ b c)
    (recipSecantTripleDomainLast_inputs W hΔ b c)
    (recipSecantTripleDomainLeft_inputs W hΔ b c)
    (recipSecantTripleDomainRight_inputs W hΔ b c)

end FLT.Mazur.WeierstrassIntegralChart
