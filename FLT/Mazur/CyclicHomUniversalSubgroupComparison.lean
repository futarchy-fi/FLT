/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicHomSubgroupPullback
public import FLT.Mazur.CyclicHomLocusEquationUniversal

/-!
# Original orbit subgroups are pullbacks of the actual universal subgroup

A parameter's global factorization identifies the full original subgroup
with the universal subgroup pulled back along that factorization. The
comparison retains both the whole curve and the actual subgroup inclusion.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.UniversalWeierstrass
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] {T : Scheme}
  (q : T ⟶ cyclicHomUniversalMultiplicationLocus n)

/-- Every full orbit subgroup on a locus test is the actual pulled universal subgroup. -/
def cyclicHomUniversalSubgroupIsoOfIdeal
    (J : (cyclicHomSourceCurve n
      (q ≫ cyclicHomUniversalMultiplicationLocusInclusion n)).FiniteSubgroup n)
    (hJ : J.ideal = cyclicHomSourceIdeal n
      (q ≫ cyclicHomUniversalMultiplicationLocusInclusion n)) :
    CompatibleIso ((cyclicHomUniversalSubgroup n).baseChange q) J :=
  (cyclicHomSubgroupPullbackIso n (cyclicHomUniversalMultiplicationLocusInclusion n)
    q (cyclicHomUniversalLocus_equation_zero n)).symm.trans
      (compatibleIsoOfIdealEq _ J ((cyclicHomSubgroup_ideal n _ _).trans hJ.symm))

/-- The original factorization identifies its unchanged subgroup with the universal one. -/
def cyclicHomUniversalSubgroupIsoOfFactorization
    (f : T ⟶ (cyclicHomAuxiliaryScheme n).left)
    (hq : q ≫ cyclicHomUniversalMultiplicationLocusInclusion n = f)
    (J : (cyclicHomSourceCurve n f).FiniteSubgroup n)
    (hJ : J.ideal = cyclicHomSourceIdeal n f) :
    CompatibleIso ((cyclicHomUniversalSubgroup n).baseChange q) J := by
  subst f
  exact cyclicHomUniversalSubgroupIsoOfIdeal n q J hJ

end FLT.Mazur.UniversalWeierstrass
