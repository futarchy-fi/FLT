/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassCyclicNormalizationFixed

/-!
# Sourcewise retraction onto the actual full cyclic slice

Every point of the closed full slice has a normalized auxiliary frame. The
constructed full normalization fixes that point and is idempotent on all
actual source families. These statements retain every cyclic label.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.UniversalWeierstrass
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (n : ℕ) [NeZero n] {T : Scheme}

/-- Every family in the actual full closed slice satisfies the original frame equations. -/
theorem cyclicNormalizedSliceFamily_satisfies (l : T ⟶ cyclicNormalizedSlice n) :
    SatisfiesNormalization
      (cyclicSchemeAuxiliaryPoint n (l ≫ cyclicNormalizedSliceInclusion n)).appTop.hom := by
  change SatisfiesNormalization
    ((l ≫ cyclicNormalizedSliceInclusion n) ≫ (forgetCyclic n).left).appTop.hom
  rw [Category.assoc, cyclicNormalizedSlice_square, ← Category.assoc]
  exact normalizedSliceFamily_satisfies (l ≫ cyclicNormalizedSliceAuxiliary n)

/-- The full point of a slice family is fixed, including every original cyclic label. -/
theorem cyclicSchemeNormalizedPoint_restrict (l : T ⟶ cyclicNormalizedSlice n) :
    cyclicSchemeNormalizedPoint n (l ≫ cyclicNormalizedSliceInclusion n) =
      l ≫ cyclicNormalizedSliceInclusion n :=
  cyclicSchemeNormalizedPoint_fixed n _ (cyclicNormalizedSliceFamily_satisfies n l)

/-- Normalization into the actual closed full slice is a retraction on every source scheme. -/
theorem cyclicSchemeNormalizedSlicePoint_restrict (l : T ⟶ cyclicNormalizedSlice n) :
    cyclicSchemeNormalizedSlicePoint n (l ≫ cyclicNormalizedSliceInclusion n) = l := by
  apply (cancel_mono (cyclicNormalizedSliceInclusion n)).mp
  rw [cyclicSchemeNormalizedSlicePoint_inclusion, cyclicSchemeNormalizedPoint_restrict]

/-- Every constructed normalized full point satisfies the original auxiliary frame equations. -/
theorem cyclicSchemeNormalizedPoint_satisfies (f : T ⟶ (cyclicAuxiliaryScheme n).left) :
    SatisfiesNormalization
      (cyclicSchemeAuxiliaryPoint n (cyclicSchemeNormalizedPoint n f)).appTop.hom := by
  change SatisfiesNormalization
    (cyclicSchemeNormalizedPoint n f ≫ (forgetCyclic n).left).appTop.hom
  rw [cyclicSchemeNormalizedPoint_forget]
  exact auxiliarySchemeNormalizedPoint_satisfies (cyclicSchemeAuxiliaryPoint n f)

/-- Repeated evaluation of full normalization fixes the actual complete source point. -/
theorem cyclicSchemeNormalizedPoint_idempotent (f : T ⟶ (cyclicAuxiliaryScheme n).left) :
    cyclicSchemeNormalizedPoint n (cyclicSchemeNormalizedPoint n f) =
      cyclicSchemeNormalizedPoint n f :=
  cyclicSchemeNormalizedPoint_fixed n _ (cyclicSchemeNormalizedPoint_satisfies n f)

/-- Repeated full normalization also fixes the actual closed-slice factorization. -/
theorem cyclicSchemeNormalizedSlicePoint_idempotent
    (f : T ⟶ (cyclicAuxiliaryScheme n).left) :
    cyclicSchemeNormalizedSlicePoint n (cyclicSchemeNormalizedPoint n f) =
      cyclicSchemeNormalizedSlicePoint n f := by
  apply (cancel_mono (cyclicNormalizedSliceInclusion n)).mp
  rw [cyclicSchemeNormalizedSlicePoint_inclusion, cyclicSchemeNormalizedSlicePoint_inclusion,
    cyclicSchemeNormalizedPoint_idempotent]

end FLT.Mazur.UniversalWeierstrass
