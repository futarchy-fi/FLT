/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassCyclicSliceRetraction

/-!
# The full cyclic slice represents normalized faithful families

The original full scheme point factors uniquely through the closed slice
exactly when its auxiliary frame satisfies the four normalization equations.
The represented bijection is natural in every source scheme.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.UniversalWeierstrass
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (n : ℕ) [NeZero n] {T : Scheme}

/-- Lift the entire original point whenever its actual auxiliary frame is normalized. -/
def cyclicNormalizedSliceFamilyLift (f : T ⟶ (cyclicAuxiliaryScheme n).left)
    (hn : SatisfiesNormalization (cyclicSchemeAuxiliaryPoint n f).appTop.hom) :
    T ⟶ cyclicNormalizedSlice n :=
  pullback.lift f (normalizedSliceFamilyLift (cyclicSchemeAuxiliaryPoint n f) hn)
    (normalizedSliceFamilyLift_inclusion (cyclicSchemeAuxiliaryPoint n f) hn).symm

/-- Factoring through the full slice preserves the entire original scheme point. -/
@[reassoc] theorem cyclicNormalizedSliceFamilyLift_inclusion
    (f : T ⟶ (cyclicAuxiliaryScheme n).left)
    (hn : SatisfiesNormalization (cyclicSchemeAuxiliaryPoint n f).appTop.hom) :
    cyclicNormalizedSliceFamilyLift n f hn ≫ cyclicNormalizedSliceInclusion n = f :=
  pullback.lift_fst ..

/-- The actual full closed slice represents normalized full families uniquely. -/
theorem cyclicNormalizedSliceFamily_iff (f : T ⟶ (cyclicAuxiliaryScheme n).left) :
    SatisfiesNormalization (cyclicSchemeAuxiliaryPoint n f).appTop.hom ↔
      ∃! l : T ⟶ cyclicNormalizedSlice n, l ≫ cyclicNormalizedSliceInclusion n = f := by
  constructor
  · intro hn
    refine ⟨cyclicNormalizedSliceFamilyLift n f hn,
      cyclicNormalizedSliceFamilyLift_inclusion n f hn, ?_⟩
    intro l hl
    exact (cancel_mono (cyclicNormalizedSliceInclusion n)).mp
      (hl.trans (cyclicNormalizedSliceFamilyLift_inclusion n f hn).symm)
  · rintro ⟨l, rfl, _⟩
    exact cyclicNormalizedSliceFamily_satisfies n l

/-- The represented bijection keeps the original coefficients and all cyclic labels. -/
def cyclicNormalizedSliceFamilyRepresentation :
    (T ⟶ cyclicNormalizedSlice n) ≃
      {f : T ⟶ (cyclicAuxiliaryScheme n).left //
        SatisfiesNormalization (cyclicSchemeAuxiliaryPoint n f).appTop.hom} where
  toFun l := ⟨l ≫ cyclicNormalizedSliceInclusion n, cyclicNormalizedSliceFamily_satisfies n l⟩
  invFun f := cyclicNormalizedSliceFamilyLift n f.val f.property
  left_inv l := (cancel_mono (cyclicNormalizedSliceInclusion n)).mp
    (cyclicNormalizedSliceFamilyLift_inclusion n (l ≫ cyclicNormalizedSliceInclusion n)
      (cyclicNormalizedSliceFamily_satisfies n l))
  right_inv f := Subtype.ext (cyclicNormalizedSliceFamilyLift_inclusion n f.val f.property)

/-- The represented full-family bijection is natural in the original source scheme. -/
theorem cyclicNormalizedSliceFamilyRepresentation_natural {U : Scheme} (k : U ⟶ T)
    (l : T ⟶ cyclicNormalizedSlice n) :
    (cyclicNormalizedSliceFamilyRepresentation n (k ≫ l)).val =
      k ≫ (cyclicNormalizedSliceFamilyRepresentation n l).val := Category.assoc ..

/-- The constructed normalization agrees with the unique original factorization on the slice. -/
theorem cyclicSchemeNormalizedSlicePoint_eq_lift (f : T ⟶ (cyclicAuxiliaryScheme n).left)
    (hn : SatisfiesNormalization (cyclicSchemeAuxiliaryPoint n f).appTop.hom) :
    cyclicSchemeNormalizedSlicePoint n f = cyclicNormalizedSliceFamilyLift n f hn := by
  apply (cancel_mono (cyclicNormalizedSliceInclusion n)).mp
  rw [cyclicSchemeNormalizedSlicePoint_inclusion, cyclicNormalizedSliceFamilyLift_inclusion,
    cyclicSchemeNormalizedPoint_fixed n f hn]

end FLT.Mazur.UniversalWeierstrass
