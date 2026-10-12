/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicHomMultiplicationPullback
public import FLT.Mazur.CyclicHomMultiplicationLocusUniversal

/-!
# The global cyclic locus represents the original multiplication equation

The actual cartesian product comparison turns the generic universal vanishing
property into the equation for the source reconstructed from each parameter.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.UniversalWeierstrass
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n]

/-- The universal closed locus represents the original full multiplication equation. -/
theorem cyclicHomUniversalLocus_factorization_iff_equation {T : Scheme}
    (f : T ⟶ (cyclicHomAuxiliaryScheme n).left) :
    (∃ k : T ⟶ cyclicHomUniversalMultiplicationLocus n,
      k ≫ cyclicHomUniversalMultiplicationLocusInclusion n = f) ↔
        cyclicHomMultiplicationEquation n f = 0 := by
  rw [cyclicHomMultiplicationEquation_iff_ideal]
  have h := FiniteFlatIdealVanishing.locus_factorization_iff
    (cyclicHomDivisorProductPullbackMap_isPullback n (𝟙 _) f)
    (cyclicHomMultiplicationIdeal n (𝟙 _))
  simpa only [← cyclicHomMultiplicationIdeal_pullback, Category.comp_id] using! h

/-- On the universal locus, the actual reconstructed source satisfies multiplication. -/
theorem cyclicHomUniversalLocus_equation_zero :
    cyclicHomMultiplicationEquation n (cyclicHomUniversalMultiplicationLocusInclusion n) = 0 :=
  (cyclicHomUniversalLocus_factorization_iff_equation n _).mp ⟨𝟙 _, Category.id_comp _⟩

/-- An original parameter satisfying multiplication has its canonical global factorization. -/
def cyclicHomUniversalLocusLift {T : Scheme}
    (f : T ⟶ (cyclicHomAuxiliaryScheme n).left)
    (h : cyclicHomMultiplicationEquation n f = 0) : T ⟶ cyclicHomUniversalMultiplicationLocus n :=
  ((cyclicHomUniversalLocus_factorization_iff_equation n f).mpr h).choose

/-- The factorization preserves the exact original parameter map. -/
@[reassoc] theorem cyclicHomUniversalLocusLift_inclusion {T : Scheme}
    (f : T ⟶ (cyclicHomAuxiliaryScheme n).left)
    (h : cyclicHomMultiplicationEquation n f = 0) :
    cyclicHomUniversalLocusLift n f h ≫ cyclicHomUniversalMultiplicationLocusInclusion n = f :=
  ((cyclicHomUniversalLocus_factorization_iff_equation n f).mpr h).choose_spec

/-- The universal finite subgroup on the actual global multiplication locus. -/
def cyclicHomUniversalSubgroup :
    (cyclicHomSourceCurve n (cyclicHomUniversalMultiplicationLocusInclusion n)).FiniteSubgroup n :=
  cyclicHomSubgroup n _ (cyclicHomUniversalLocus_equation_zero n)

/-- The universal subgroup retains the entire cyclic orbit ideal. -/
theorem cyclicHomUniversalSubgroup_ideal :
    (cyclicHomUniversalSubgroup n).ideal =
      cyclicHomSourceIdeal n (cyclicHomUniversalMultiplicationLocusInclusion n) :=
  cyclicHomSubgroup_ideal n _ _

end FLT.Mazur.UniversalWeierstrass
