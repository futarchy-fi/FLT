/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassCyclicHomNormalizedSlice

/-!
# Sourcewise retraction onto the actual full cyclic slice

Every point of the closed full slice has a normalized auxiliary frame. The
constructed full normalization fixes that point and is idempotent on all
actual source families. These statements retain every cyclic label.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.OddWeierstrassParameter
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (n : ℕ) [NeZero n] {T : Scheme}

/-- Every family in the actual full closed slice satisfies the original frame equations. -/
theorem cyclicHomNormalizedSliceFamily_satisfies (l : T ⟶ cyclicHomNormalizedSlice n) :
    SatisfiesNormalization
      (cyclicHomAuxiliaryPoint n (l ≫ cyclicHomNormalizedSliceInclusion n)).appTop.hom := by
  change SatisfiesNormalization
    ((l ≫ cyclicHomNormalizedSliceInclusion n) ≫ (cyclicHomAuxiliary n).left).appTop.hom
  rw [Category.assoc, cyclicHomNormalizedSlice_square, ← Category.assoc]
  exact normalizedSliceFamily_satisfies (l ≫ cyclicHomNormalizedSliceAuxiliary n)

/-- The full point of a slice family is fixed, including every original cyclic label. -/
theorem cyclicHomNormalizedPoint_restrict (l : T ⟶ cyclicHomNormalizedSlice n) :
    cyclicHomNormalizedPoint n (l ≫ cyclicHomNormalizedSliceInclusion n) =
      l ≫ cyclicHomNormalizedSliceInclusion n :=
  cyclicHomNormalizedPoint_fixed n _ (cyclicHomNormalizedSliceFamily_satisfies n l)

/-- Normalization into the actual closed full slice is a retraction on every source scheme. -/
theorem cyclicHomNormalizedSlicePoint_restrict (l : T ⟶ cyclicHomNormalizedSlice n) :
    cyclicHomNormalizedSlicePoint n (l ≫ cyclicHomNormalizedSliceInclusion n) = l := by
  apply (cancel_mono (cyclicHomNormalizedSliceInclusion n)).mp
  rw [cyclicHomNormalizedSlicePoint_inclusion, cyclicHomNormalizedPoint_restrict]

/-- Every constructed normalized full point satisfies the original auxiliary frame equations. -/
theorem cyclicHomNormalizedPoint_satisfies (f : T ⟶ (cyclicHomAuxiliaryScheme n).left) :
    SatisfiesNormalization
      (cyclicHomAuxiliaryPoint n (cyclicHomNormalizedPoint n f)).appTop.hom := by
  change SatisfiesNormalization
    (cyclicHomNormalizedPoint n f ≫ (cyclicHomAuxiliary n).left).appTop.hom
  rw [cyclicHomNormalizedPoint_auxiliary]
  exact auxiliarySchemeNormalizedPoint_satisfies (cyclicHomAuxiliaryPoint n f)

/-- Repeated full normalization also fixes the actual closed-slice factorization. -/
theorem cyclicHomNormalizedSlicePoint_idempotent
    (f : T ⟶ (cyclicHomAuxiliaryScheme n).left) :
    cyclicHomNormalizedSlicePoint n (cyclicHomNormalizedPoint n f) =
      cyclicHomNormalizedSlicePoint n f := by
  apply (cancel_mono (cyclicHomNormalizedSliceInclusion n)).mp
  rw [cyclicHomNormalizedSlicePoint_inclusion, cyclicHomNormalizedSlicePoint_inclusion,
    cyclicHomNormalizedPoint_idempotent]

end FLT.Mazur.OddWeierstrassParameter
