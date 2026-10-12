/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicHomMultiplicationPullback
public import FLT.Mazur.RetainedSubgroupCartierMarking

/-!
# The actual cyclic orbit subgroup commutes with parameter change

Multiplication vanishing survives arbitrary base change. The reconstructed
subgroup agrees with the original pulled subgroup through the full curve
comparison and equality of the actual closed ideals.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.UniversalWeierstrass
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] {T U : Scheme}
  (f : T ⟶ (cyclicHomAuxiliaryScheme n).left) (k : U ⟶ T)
  (h : cyclicHomMultiplicationEquation n f = 0)

include h in
/-- Arbitrary parameter pullback preserves the whole multiplication equation. -/
theorem cyclicHomMultiplicationEquation_zero_comp :
    cyclicHomMultiplicationEquation n (k ≫ f) = 0 := by
  rw [cyclicHomMultiplicationEquation_iff_ideal, cyclicHomMultiplicationIdeal_pullback,
    (cyclicHomMultiplicationEquation_iff_ideal n f).mp h,
    Scheme.IdealSheafData.comap_bot]

/-- The retained pullback subgroup has exactly the reconstructed full orbit ideal. -/
theorem cyclicHomSubgroup_retained_ideal :
    (((cyclicHomSubgroup n f h).baseChange k).transport
      (cyclicHomSourcePullbackIso n f k).symm).ideal = cyclicHomSourceIdeal n (k ≫ f) := by
  let H := (cyclicHomSubgroup n f h).baseChange k
  let a := H.transportCompatibleIso (cyclicHomSourcePullbackIso n f k).symm
  have hi := ideal_transport H _ a.curve a.subgroup a.compatible
  change _ = (H.ideal).comap (cyclicHomSourcePullbackIso n f k).hom.curve.left at hi
  rw [show H.ideal = (cyclicHomSourceIdeal n f).comap
    (pullback.fst (cyclicHomSourceCurve n f).curve.hom k) by
      rw [baseChange_ideal, cyclicHomSubgroup_ideal]] at hi
  rw [← Scheme.IdealSheafData.comap_comp] at hi
  exact hi.trans (cyclicHomSourceIdeal_pullback n f k).symm

/-- Full compatible comparison with the actual original pulled subgroup. -/
def cyclicHomSubgroupPullbackIso :
    CompatibleIso (cyclicHomSubgroup n (k ≫ f)
      (cyclicHomMultiplicationEquation_zero_comp n f k h))
      ((cyclicHomSubgroup n f h).baseChange k) :=
  (compatibleIsoOfIdealEq _ _ ((cyclicHomSubgroup_ideal n _ _).trans
    (cyclicHomSubgroup_retained_ideal n f k h).symm)).trans
      (((cyclicHomSubgroup n f h).baseChange k).transportCompatibleIso
        (cyclicHomSourcePullbackIso n f k).symm).symm

end FLT.Mazur.UniversalWeierstrass
