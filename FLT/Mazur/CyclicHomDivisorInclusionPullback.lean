/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicHomDivisorPullback

/-!
# Compatibility of cyclic divisor and curve comparisons

The comparison of the full closed divisor preserves its actual inclusion
in the pulled-back source curve, as a morphism over the test base.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.UniversalWeierstrass
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] {T U : Scheme}
  (f : T ⟶ (cyclicHomAuxiliaryScheme n).left) (k : U ⟶ T)

/-- The actual closed divisor inclusions commute with the full source comparison. -/
theorem cyclicHomDivisorPullbackIso_inclusion :
    ClosedGroupIdeal.inclusion (cyclicHomSourceCurve n (k ≫ f)).curve
        (cyclicHomSourceIdeal n (k ≫ f)) ≫ (cyclicHomSourcePullbackIso n f k).hom.curve =
      (cyclicHomDivisorPullbackIso n f k).hom ≫ (Over.pullback k).map
        (ClosedGroupIdeal.inclusion (cyclicHomSourceCurve n f).curve
          (cyclicHomSourceIdeal n f)) := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simp only [Over.comp_left, Category.assoc, Over.pullback_map_left,
      pullback.lift_fst]
    rw [cyclicHomDivisorPullbackIso_fst_assoc]
    exact (cyclicHomDivisorPullbackMap_inclusion n f k).symm
  · exact Over.w _ |>.trans (Over.w _).symm

end FLT.Mazur.UniversalWeierstrass
