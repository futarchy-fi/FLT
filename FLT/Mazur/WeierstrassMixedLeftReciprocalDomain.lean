/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassMixedLeftReciprocalGlobal
public import FLT.Mazur.WeierstrassReciprocalTripleDomain

/-!
# Genuine mixed left reciprocal triple intersections

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

/-- The genuine intersection with only the left outer law reciprocal. -/
abbrev MixedLeftRecipDomain (b c d e : Bool) :=
  pullback (ordinaryGlobalDomain W e)
    (recipTripleOuterLeftMap W hΔ b c d ≫ integralCurveAddLastPair W hΔ)

/-- Inclusion of the actual four-domain intersection into the triple product. -/
def mixedLeftRecipDomainMap (b c d e : Bool) :
    MixedLeftRecipDomain W hΔ b c d e ⟶ integralCurveTriple W :=
  pullback.snd _ _ ≫ recipTripleOuterLeftMap W hΔ b c d

instance mixedLeftRecipDomainMap_isOpenImmersion (b c d e : Bool) :
    IsOpenImmersion (mixedLeftRecipDomainMap W hΔ b c d e) := by
  unfold mixedLeftRecipDomainMap recipTripleOuterLeftMap ordinaryTripleInnerMap
  infer_instance

/-- Projection to the first ordinary inner chart. -/
def mixedLeftRecipDomainFirst (b c d e : Bool) : MixedLeftRecipDomain W hΔ b c d e ⟶
    Spec (additionChartRing W (ordinaryIndex b)) :=
  pullback.snd _ _ ≫ pullback.snd _ _ ≫ pullback.snd _ _ ≫ pullback.fst _ _

/-- Projection to the second ordinary inner chart. -/
def mixedLeftRecipDomainLast (b c d e : Bool) : MixedLeftRecipDomain W hΔ b c d e ⟶
    Spec (additionChartRing W (ordinaryIndex c)) :=
  pullback.snd _ _ ≫ pullback.snd _ _ ≫ pullback.fst _ _

/-- Projection to the left outer reciprocal chart. -/
def mixedLeftRecipDomainLeft (b c d e : Bool) : MixedLeftRecipDomain W hΔ b c d e ⟶
    Spec (additionChartRing W (reciprocalIndex d)) :=
  pullback.snd _ _ ≫ pullback.fst _ _

/-- Projection to the right outer ordinary chart. -/
abbrev mixedLeftRecipDomainRight (b c d e : Bool) : MixedLeftRecipDomain W hΔ b c d e ⟶
    Spec (additionChartRing W (ordinaryIndex e)) := pullback.fst _ _

/-- The first chart carries the original first pair. -/
theorem mixedLeftRecipDomainFirst_inputs (b c d e : Bool) :
    mixedLeftRecipDomainFirst W hΔ b c d e ≫ ordinaryGlobalDomain W b =
      mixedLeftRecipDomainMap W hΔ b c d e ≫ integralCurveTriplePair W := by
  simp only [mixedLeftRecipDomainFirst, mixedLeftRecipDomainMap,
    recipTripleOuterLeftMap,
    ordinaryTripleInnerMap, Category.assoc]
  rw [pullback.condition]

/-- The last chart carries the original last pair. -/
theorem mixedLeftRecipDomainLast_inputs (b c d e : Bool) :
    mixedLeftRecipDomainLast W hΔ b c d e ≫ ordinaryGlobalDomain W c =
      mixedLeftRecipDomainMap W hΔ b c d e ≫ integralCurveTripleLastPair W := by
  simp only [mixedLeftRecipDomainLast, mixedLeftRecipDomainMap, recipTripleOuterLeftMap,
    ordinaryTripleInnerMap, Category.assoc]
  simp only [pullback.condition]

/-- The left outer chart carries the actual first sum and third input. -/
theorem mixedLeftRecipDomainLeft_inputs (b c d e : Bool) :
    mixedLeftRecipDomainLeft W hΔ b c d e ≫ reciprocalGlobalDomain W d =
      mixedLeftRecipDomainMap W hΔ b c d e ≫ integralCurveAddFirstPair W hΔ := by
  simp only [mixedLeftRecipDomainLeft, mixedLeftRecipDomainMap, recipTripleOuterLeftMap,
    Category.assoc]
  simp only [pullback.condition]

/-- The right outer chart carries the actual first input and last sum. -/
theorem mixedLeftRecipDomainRight_inputs (b c d e : Bool) :
    mixedLeftRecipDomainRight W hΔ b c d e ≫ ordinaryGlobalDomain W e =
      mixedLeftRecipDomainMap W hΔ b c d e ≫ integralCurveAddLastPair W hΔ := by
  exact pullback.condition.trans (Category.assoc _ _ _).symm

/-- Associativity holds on the genuine four-chart intersection. -/
theorem mixedLeftRecipDomain_associativity (b c d e : Bool) :
    mixedLeftRecipDomainMap W hΔ b c d e ≫ integralCurveTripleAddLeft W hΔ =
      mixedLeftRecipDomainMap W hΔ b c d e ≫ integralCurveTripleAddRight W hΔ :=
  integralCurveTripleAdd_mixedLeftReciprocal W hΔ (mixedLeftRecipDomainMap W hΔ b c d e) b c d e
    (mixedLeftRecipDomainFirst W hΔ b c d e) (mixedLeftRecipDomainLast W hΔ b c d e)
    (mixedLeftRecipDomainLeft W hΔ b c d e) (mixedLeftRecipDomainRight W hΔ b c d e)
    (mixedLeftRecipDomainFirst_inputs W hΔ b c d e)
    (mixedLeftRecipDomainLast_inputs W hΔ b c d e)
    (mixedLeftRecipDomainLeft_inputs W hΔ b c d e)
    (mixedLeftRecipDomainRight_inputs W hΔ b c d e)

end FLT.Mazur.WeierstrassIntegralChart
