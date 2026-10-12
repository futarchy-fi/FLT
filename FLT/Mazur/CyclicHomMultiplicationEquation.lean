/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicHomSourceDivisor
public import FLT.Mazur.CyclicDivisorSubgroupCriterion

/-!
# The actual subgroup equation on cyclic homomorphism parameters

This is the pulled Cartier ideal map on the full orbit-divisor product.
Its zero tests are exactly the parameters whose actual orbit divisor is a
finite subgroup, with no distinctness or etaleness condition on the marking.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.UniversalWeierstrass
open GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] {T : Scheme} (f : T ⟶ (cyclicHomAuxiliaryScheme n).left)

local instance : Smooth (cyclicHomSourceCurve n f).curve.hom :=
  SmoothOfRelativeDimension.smooth 1 _

/-- The actual multiplication obstruction of the multiplicity-preserving source divisor. -/
def cyclicHomMultiplicationEquation :=
  (cyclicHomSourceCurve n f).cyclicDivisorMultiplicationEquation (cyclicHomSourceMarking n f)

/-- A zero equation constructs the actual source subgroup on this parameter. -/
def cyclicHomSubgroup (h : cyclicHomMultiplicationEquation n f = 0) :
    (cyclicHomSourceCurve n f).FiniteSubgroup n :=
  (cyclicHomSourceCurve n f).subgroupOfCyclicMultiplication (cyclicHomSourceMarking n f) h

/-- The constructed subgroup keeps the actual universal source ideal. -/
theorem cyclicHomSubgroup_ideal (h : cyclicHomMultiplicationEquation n f = 0) :
    (cyclicHomSubgroup n f h).ideal = cyclicHomSourceIdeal n f :=
  (cyclicHomSourceCurve n f).subgroupOfCyclicMultiplication_ideal (cyclicHomSourceMarking n f) h

/-- On every test, the equation is exactly the non-etale subgroup condition. -/
theorem cyclicHomMultiplicationEquation_iff_subgroup :
    cyclicHomMultiplicationEquation n f = 0 ↔
      ∃ H : (cyclicHomSourceCurve n f).FiniteSubgroup n, H.ideal = cyclicHomSourceIdeal n f :=
  (cyclicHomSourceCurve n f).cyclicDivisorMultiplicationEquation_iff_subgroup
    (cyclicHomSourceMarking n f)

/-- Any retained original subgroup kills the full multiplication equation. -/
theorem cyclicHomMultiplicationEquation_of_subgroup
    (H : (cyclicHomSourceCurve n f).FiniteSubgroup n)
    (hI : H.ideal = cyclicHomSourceIdeal n f) : cyclicHomMultiplicationEquation n f = 0 :=
  (cyclicHomMultiplicationEquation_iff_subgroup n f).mpr ⟨H, hI⟩

end FLT.Mazur.UniversalWeierstrass
