/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassCyclicHomUniversalSubgroupComparison
public import FLT.Mazur.OddWeierstrassCyclicHomPullbackAuxiliaryMarking

/-!
# Odd-chart universal subgroup comparison retains the auxiliary frame

The full factorization comparison carries the pulled universal auxiliary
sections to the independent original markings, for every source subgroup
with the specified orbit ideal.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.OddWeierstrassParameter
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup GroupSectionBaseChange
open UniversalWeierstrass (Labels)
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n]

/-- The independent auxiliary marking on the universal multiplication locus. -/
def cyclicHomUniversalAuxiliaryMarking (i : Labels 3) :
    𝟙_ (Over (cyclicHomUniversalMultiplicationLocus n)) ⟶
      (cyclicHomSourceCurve n (cyclicHomUniversalMultiplicationLocusInclusion n)).group :=
  auxiliarySchemeMarking
    (cyclicHomAuxiliaryPoint n (cyclicHomUniversalMultiplicationLocusInclusion n)) i

variable {T : Scheme} (q : T ⟶ cyclicHomUniversalMultiplicationLocus n)

/-- The inverse universal pullback comparison retains the independent auxiliary sections. -/
theorem cyclicHomUniversalSubgroupIsoOfIdeal_auxiliary
    (J : (cyclicHomSourceCurve n
      (q ≫ cyclicHomUniversalMultiplicationLocusInclusion n)).FiniteSubgroup n)
    (hJ : J.ideal = cyclicHomSourceIdeal n
      (q ≫ cyclicHomUniversalMultiplicationLocusInclusion n)) (i : Labels 3) :
    pullSection q (cyclicHomUniversalAuxiliaryMarking n i) ≫
      (cyclicHomUniversalSubgroupIsoOfIdeal n q J hJ).curve.hom.group =
        auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n
          (q ≫ cyclicHomUniversalMultiplicationLocusInclusion n)) i := by
  let a := cyclicHomSubgroupPullbackIso n (cyclicHomUniversalMultiplicationLocusInclusion n)
    q (cyclicHomUniversalLocus_equation_zero n)
  have ha := cyclicHomSubgroupPullbackIso_auxiliary n
    (cyclicHomUniversalMultiplicationLocusInclusion n) q
    (cyclicHomUniversalLocus_equation_zero n) i
  change _ ≫ a.curve.hom.group = pullSection q (cyclicHomUniversalAuxiliaryMarking n i) at ha
  change _ ≫ (a.curve.inv.group ≫ 𝟙 _) = _
  rw [Category.comp_id, ← ha, Category.assoc]
  have hi : a.curve.hom.group ≫ a.curve.inv.group = 𝟙 _ :=
    congrArg Hom.group a.curve.hom_inv_id
  rw [hi, Category.comp_id]

/-- Factoring through the actual closed locus preserves every original auxiliary label. -/
theorem cyclicHomUniversalSubgroupIsoOfFactorization_auxiliary
    (f : T ⟶ (cyclicHomAuxiliaryScheme n).left)
    (hq : q ≫ cyclicHomUniversalMultiplicationLocusInclusion n = f)
    (J : (cyclicHomSourceCurve n f).FiniteSubgroup n)
    (hJ : J.ideal = cyclicHomSourceIdeal n f) (i : Labels 3) :
    pullSection q (cyclicHomUniversalAuxiliaryMarking n i) ≫
      (cyclicHomUniversalSubgroupIsoOfFactorization n q f hq J hJ).curve.hom.group =
        auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n f) i := by
  subst f
  exact cyclicHomUniversalSubgroupIsoOfIdeal_auxiliary n q J hJ i

end FLT.Mazur.OddWeierstrassParameter
