/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassMixedRightReciprocalGlobal
public import FLT.Mazur.WeierstrassAllOrdinaryTripleDomain

/-!
# Genuine mixed right reciprocal triple intersections

Pull back both actual outer domains over the common ordinary inner domain.
Associativity holds on this open without supplied output-unit or compatibility hypotheses.
No assertion that these opens cover the full triple product is made.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

variable (hΔ : IsUnit W.Δ)

/-- The genuine intersection with only the right outer law reciprocal. -/
abbrev MixedRightRecipDomain (b c d e : Bool) :=
  pullback (reciprocalGlobalDomain W e)
    (allOrdinaryTripleOuterLeftMap W hΔ b c d ≫ integralCurveAddLastPair W hΔ)

/-- Inclusion of the actual four-domain intersection into the triple product. -/
def mixedRightRecipDomainMap (b c d e : Bool) :
    MixedRightRecipDomain W hΔ b c d e ⟶ integralCurveTriple W :=
  pullback.snd _ _ ≫ allOrdinaryTripleOuterLeftMap W hΔ b c d

instance mixedRightRecipDomainMap_isOpenImmersion (b c d e : Bool) :
    IsOpenImmersion (mixedRightRecipDomainMap W hΔ b c d e) := by
  unfold mixedRightRecipDomainMap allOrdinaryTripleOuterLeftMap ordinaryTripleInnerMap
  infer_instance

/-- Projection to the first ordinary inner chart. -/
def mixedRightRecipDomainFirst (b c d e : Bool) : MixedRightRecipDomain W hΔ b c d e ⟶
    Spec (additionChartRing W (ordinaryIndex b)) :=
  pullback.snd _ _ ≫ pullback.snd _ _ ≫ pullback.snd _ _ ≫ pullback.fst _ _

/-- Projection to the second ordinary inner chart. -/
def mixedRightRecipDomainLast (b c d e : Bool) : MixedRightRecipDomain W hΔ b c d e ⟶
    Spec (additionChartRing W (ordinaryIndex c)) :=
  pullback.snd _ _ ≫ pullback.snd _ _ ≫ pullback.fst _ _

/-- Projection to the left outer ordinary chart. -/
def mixedRightRecipDomainLeft (b c d e : Bool) : MixedRightRecipDomain W hΔ b c d e ⟶
    Spec (additionChartRing W (ordinaryIndex d)) :=
  pullback.snd _ _ ≫ pullback.fst _ _

/-- Projection to the right outer reciprocal chart. -/
abbrev mixedRightRecipDomainRight (b c d e : Bool) : MixedRightRecipDomain W hΔ b c d e ⟶
    Spec (additionChartRing W (reciprocalIndex e)) := pullback.fst _ _

/-- The first chart carries the original first pair. -/
theorem mixedRightRecipDomainFirst_inputs (b c d e : Bool) :
    mixedRightRecipDomainFirst W hΔ b c d e ≫ ordinaryGlobalDomain W b =
      mixedRightRecipDomainMap W hΔ b c d e ≫ integralCurveTriplePair W := by
  simp only [mixedRightRecipDomainFirst, mixedRightRecipDomainMap,
    allOrdinaryTripleOuterLeftMap,
    ordinaryTripleInnerMap, Category.assoc]
  rw [pullback.condition]

/-- The last chart carries the original last pair. -/
theorem mixedRightRecipDomainLast_inputs (b c d e : Bool) :
    mixedRightRecipDomainLast W hΔ b c d e ≫ ordinaryGlobalDomain W c =
      mixedRightRecipDomainMap W hΔ b c d e ≫ integralCurveTripleLastPair W := by
  simp only [mixedRightRecipDomainLast, mixedRightRecipDomainMap, allOrdinaryTripleOuterLeftMap,
    ordinaryTripleInnerMap, Category.assoc]
  simp only [pullback.condition]

/-- The left outer chart carries the actual first sum and third input. -/
theorem mixedRightRecipDomainLeft_inputs (b c d e : Bool) :
    mixedRightRecipDomainLeft W hΔ b c d e ≫ ordinaryGlobalDomain W d =
      mixedRightRecipDomainMap W hΔ b c d e ≫ integralCurveAddFirstPair W hΔ := by
  simp only [mixedRightRecipDomainLeft, mixedRightRecipDomainMap, allOrdinaryTripleOuterLeftMap,
    Category.assoc]
  simp only [pullback.condition]

/-- The right outer chart carries the actual first input and last sum. -/
theorem mixedRightRecipDomainRight_inputs (b c d e : Bool) :
    mixedRightRecipDomainRight W hΔ b c d e ≫ reciprocalGlobalDomain W e =
      mixedRightRecipDomainMap W hΔ b c d e ≫ integralCurveAddLastPair W hΔ := by
  exact pullback.condition.trans (Category.assoc _ _ _).symm

/-- Associativity holds on the genuine four-chart intersection. -/
theorem mixedRightRecipDomain_associativity (b c d e : Bool) :
    mixedRightRecipDomainMap W hΔ b c d e ≫ integralCurveTripleAddLeft W hΔ =
      mixedRightRecipDomainMap W hΔ b c d e ≫ integralCurveTripleAddRight W hΔ :=
  integralCurveTripleAdd_mixedRightReciprocal W hΔ (mixedRightRecipDomainMap W hΔ b c d e) b c d e
    (mixedRightRecipDomainFirst W hΔ b c d e) (mixedRightRecipDomainLast W hΔ b c d e)
    (mixedRightRecipDomainLeft W hΔ b c d e) (mixedRightRecipDomainRight W hΔ b c d e)
    (mixedRightRecipDomainFirst_inputs W hΔ b c d e)
    (mixedRightRecipDomainLast_inputs W hΔ b c d e)
    (mixedRightRecipDomainLeft_inputs W hΔ b c d e)
    (mixedRightRecipDomainRight_inputs W hΔ b c d e)

end FLT.Mazur.WeierstrassIntegralChart
