/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassCyclicHomUniversalSubgroupComparison
public import FLT.Mazur.OddWeierstrassCyclicHomSubgroupPullbackMarking
public import FLT.Mazur.OddWeierstrassCyclicHomPrescribedGeneratorComparison
public import FLT.Mazur.OrbitGeneratorCurveMarking

/-!
# Odd closed-locus factorization retains the prescribed generator

The actual universal subgroup has its specified orbit generator. The full
comparison along a factorization carries that pulled generator to the
original section determined by the same curve marking.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.OddWeierstrassParameter
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup GroupSectionBaseChange
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n]

/-- The specified label-one section of the actual universal subgroup. -/
def cyclicHomUniversalGenerator : 𝟙_ (Over (cyclicHomUniversalMultiplicationLocus n)) ⟶
    (cyclicHomUniversalSubgroup n).carrier :=
  (cyclicHomUniversalSubgroup n).orbitGenerator
    (cyclicHomSourceMarking n (cyclicHomUniversalMultiplicationLocusInclusion n))
    (cyclicHomUniversalSubgroup_ideal n)

/-- The specified universal section is a Cartier generator, also at non-etale levels. -/
theorem cyclicHomUniversalGenerator_cartier :
    (cyclicHomUniversalSubgroup n).IsCartierGenerator (cyclicHomUniversalGenerator n) :=
  orbitGenerator_cartier _ _ _

variable {T : Scheme} (q : T ⟶ cyclicHomUniversalMultiplicationLocus n)
  (f : T ⟶ (cyclicHomAuxiliaryScheme n).left)
  (hq : q ≫ cyclicHomUniversalMultiplicationLocusInclusion n = f)
  (J : (cyclicHomSourceCurve n f).FiniteSubgroup n)
  (hJ : J.ideal = cyclicHomSourceIdeal n f)
  {P : 𝟙_ (Over T) ⟶ J.carrier} (hP : J.IsCartierGenerator P)
  (hφ : J.generatorCurveMarking hP = cyclicHomSourceMarking n f)

include hφ in
/-- Factoring through the actual closed locus retains the prescribed original generator. -/
theorem cyclicHomUniversalSubgroupIsoOfFactorization_generator :
    pullSection q (cyclicHomUniversalGenerator n) ≫
      (cyclicHomUniversalSubgroupIsoOfFactorization n q f hq J hJ).subgroup.hom = P := by
  subst f
  let a := cyclicHomSubgroupPullbackIso n (cyclicHomUniversalMultiplicationLocusInclusion n)
    q (cyclicHomUniversalLocus_equation_zero n)
  let b := cyclicHomPrescribedSubgroupIso n
    (q ≫ cyclicHomUniversalMultiplicationLocusInclusion n)
    (cyclicHomMultiplicationEquation_zero_comp n _ q
      (cyclicHomUniversalLocus_equation_zero n)) J hJ
  have ha := cyclicHomSubgroupPullbackIso_generator n
    (cyclicHomUniversalMultiplicationLocusInclusion n) q (cyclicHomUniversalLocus_equation_zero n)
  have hb := cyclicHomPrescribedSubgroupIso_generator n _
    (cyclicHomMultiplicationEquation_zero_comp n _ q
      (cyclicHomUniversalLocus_equation_zero n)) J hJ hP hφ
  change _ ≫ a.subgroup.hom = pullSection q (cyclicHomUniversalGenerator n) at ha
  change _ ≫ (a.subgroup.inv ≫ b.subgroup.hom) = P
  rw [← ha]
  simp only [Category.assoc, ← Category.assoc a.subgroup.hom, a.subgroup.hom_inv_id,
    Category.id_comp]
  exact hb

end FLT.Mazur.OddWeierstrassParameter
