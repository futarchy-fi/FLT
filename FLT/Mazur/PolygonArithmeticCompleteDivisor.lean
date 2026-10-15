/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticMarkingCartier
public import FLT.Mazur.RelativeSums

/-!
# The actual complete marked divisor and its base changes

The product of the original section ideals is a relative Cartier divisor.
After arbitrary base change it is exactly the product of the lifted section
ideals, and each lifted section remains relative Cartier.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.PolygonArithmeticStages

open FCurve

set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase

variable (A : Type) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]
  (π : A) (hne : π ≠ 0) (hgen : IsLocalRing.maximalIdeal A = ideal A π)
  [IsAdicComplete (ideal A π) A] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- The relative divisor formed by the actual original complete markings. -/
def completeMarkingDivisor : (exactVeroneseProj A π n h hne hgen).IdealSheafData :=
  ∏ i : Fin n, (completeBaseMarking A π hne hgen n h i).ker

/-- The original complete marked divisor is relative effective Cartier. -/
theorem completeMarkingDivisor_relativeCartier :
    RelativeEffectiveCartier (exactVeroneseProjToBase A π n h hne hgen)
      (completeMarkingDivisor A π hne hgen n h) :=
  relativeEffectiveCartier_prod _ Finset.univ _
    (fun i _ ↦ completeBaseMarking_relativeCartier A π hne hgen n h i)

variable {S : Scheme} (s : S ⟶ Spec (.of A))

/-- The actual lifted marking ideal is the pullback of its original complete ideal. -/
theorem completeFiberMarking_ker (i : Fin n) :
    (completeFiberMarking A π hne hgen n h s i).ker =
      (completeBaseMarking A π hne hgen n h i).ker.comap
        (pullback.fst (exactVeroneseProjToBase A π n h hne hgen) s) := by
  let _ := exactVeroneseProjToBase_isProper A π n h hne hgen
  exact ker_sectionBaseChange _ s _ (completeBaseMarking_toBase A π hne hgen n h i)

/-- Each actual lifted marking is relative Cartier after arbitrary scheme base change. -/
theorem completeFiberMarking_relativeCartier (i : Fin n) :
    RelativeEffectiveCartier (pullback.snd (exactVeroneseProjToBase A π n h hne hgen) s)
      (completeFiberMarking A π hne hgen n h s i).ker := by
  rw [completeFiberMarking_ker]
  exact relativeCartierBaseChange _ s _ (completeBaseMarking_relativeCartier A π hne hgen n h i)

/-- Base change of the original divisor is exactly the divisor of the actual lifted labels. -/
theorem completeMarkingDivisor_comap :
    (completeMarkingDivisor A π hne hgen n h).comap
        (pullback.fst (exactVeroneseProjToBase A π n h hne hgen) s) =
      ∏ i : Fin n, (completeFiberMarking A π hne hgen n h s i).ker := by
  simp only [completeMarkingDivisor, idealSheaf_comap_prod, completeFiberMarking_ker]

/-- The actual lifted marked divisor is relative Cartier over every new base. -/
theorem completeFiberMarkingDivisor_relativeCartier :
    RelativeEffectiveCartier (pullback.snd (exactVeroneseProjToBase A π n h hne hgen) s)
      (∏ i : Fin n, (completeFiberMarking A π hne hgen n h s i).ker) := by
  rw [← completeMarkingDivisor_comap]
  exact relativeCartierBaseChange _ s _ (completeMarkingDivisor_relativeCartier A π hne hgen n h)

end FLT.Mazur.PolygonArithmeticStages
