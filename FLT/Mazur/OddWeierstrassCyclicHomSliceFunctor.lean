/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassCyclicHomSliceRetraction

/-!
# The full cyclic slice represents normalized unrestricted families

The original full scheme point factors uniquely through the closed slice
exactly when its auxiliary frame satisfies the four normalization equations.
The represented bijection is natural in every source scheme.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.OddWeierstrassParameter
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (n : ℕ) [NeZero n] {T : Scheme}

/-- Lift the entire original point whenever its actual auxiliary frame is normalized. -/
def cyclicHomNormalizedSliceFamilyLift (f : T ⟶ (cyclicHomAuxiliaryScheme n).left)
    (hn : SatisfiesNormalization (cyclicHomAuxiliaryPoint n f).appTop.hom) :
    T ⟶ cyclicHomNormalizedSlice n :=
  pullback.lift f (normalizedSliceFamilyLift (cyclicHomAuxiliaryPoint n f) hn)
    (normalizedSliceFamilyLift_inclusion (cyclicHomAuxiliaryPoint n f) hn).symm

/-- Factoring through the full slice preserves the entire original scheme point. -/
@[reassoc] theorem cyclicHomNormalizedSliceFamilyLift_inclusion
    (f : T ⟶ (cyclicHomAuxiliaryScheme n).left)
    (hn : SatisfiesNormalization (cyclicHomAuxiliaryPoint n f).appTop.hom) :
    cyclicHomNormalizedSliceFamilyLift n f hn ≫ cyclicHomNormalizedSliceInclusion n = f :=
  pullback.lift_fst ..

/-- The actual full closed slice represents normalized full families uniquely. -/
theorem cyclicHomNormalizedSliceFamily_iff (f : T ⟶ (cyclicHomAuxiliaryScheme n).left) :
    SatisfiesNormalization (cyclicHomAuxiliaryPoint n f).appTop.hom ↔
      ∃! l : T ⟶ cyclicHomNormalizedSlice n, l ≫ cyclicHomNormalizedSliceInclusion n = f := by
  constructor
  · intro hn
    refine ⟨cyclicHomNormalizedSliceFamilyLift n f hn,
      cyclicHomNormalizedSliceFamilyLift_inclusion n f hn, ?_⟩
    intro l hl
    exact (cancel_mono (cyclicHomNormalizedSliceInclusion n)).mp
      (hl.trans (cyclicHomNormalizedSliceFamilyLift_inclusion n f hn).symm)
  · rintro ⟨l, rfl, _⟩
    exact cyclicHomNormalizedSliceFamily_satisfies n l

/-- The represented bijection keeps the original coefficients and all cyclic labels. -/
def cyclicHomNormalizedSliceFamilyRepresentation :
    (T ⟶ cyclicHomNormalizedSlice n) ≃
      {f : T ⟶ (cyclicHomAuxiliaryScheme n).left //
        SatisfiesNormalization (cyclicHomAuxiliaryPoint n f).appTop.hom} where
  toFun l := ⟨l ≫ cyclicHomNormalizedSliceInclusion n, cyclicHomNormalizedSliceFamily_satisfies n l⟩
  invFun f := cyclicHomNormalizedSliceFamilyLift n f.val f.property
  left_inv l := (cancel_mono (cyclicHomNormalizedSliceInclusion n)).mp
    (cyclicHomNormalizedSliceFamilyLift_inclusion n (l ≫ cyclicHomNormalizedSliceInclusion n)
      (cyclicHomNormalizedSliceFamily_satisfies n l))
  right_inv f := Subtype.ext (cyclicHomNormalizedSliceFamilyLift_inclusion n f.val f.property)

/-- The represented full-family bijection is natural in the original source scheme. -/
theorem cyclicHomNormalizedSliceFamilyRepresentation_natural {U : Scheme} (k : U ⟶ T)
    (l : T ⟶ cyclicHomNormalizedSlice n) :
    (cyclicHomNormalizedSliceFamilyRepresentation n (k ≫ l)).val =
      k ≫ (cyclicHomNormalizedSliceFamilyRepresentation n l).val := Category.assoc ..

/-- The constructed normalization agrees with the unique original factorization on the slice. -/
theorem cyclicHomNormalizedSlicePoint_eq_lift (f : T ⟶ (cyclicHomAuxiliaryScheme n).left)
    (hn : SatisfiesNormalization (cyclicHomAuxiliaryPoint n f).appTop.hom) :
    cyclicHomNormalizedSlicePoint n f = cyclicHomNormalizedSliceFamilyLift n f hn := by
  apply (cancel_mono (cyclicHomNormalizedSliceInclusion n)).mp
  rw [cyclicHomNormalizedSlicePoint_inclusion, cyclicHomNormalizedSliceFamilyLift_inclusion,
    cyclicHomNormalizedPoint_fixed n f hn]

/-- Normalization into the full closed slice commutes with every source morphism. -/
theorem cyclicHomNormalizedSlicePoint_natural {U : Scheme}
    (f : T ⟶ (cyclicHomAuxiliaryScheme n).left) (k : U ⟶ T) :
    cyclicHomNormalizedSlicePoint n (k ≫ f) = k ≫ cyclicHomNormalizedSlicePoint n f := by
  apply (cancel_mono (cyclicHomNormalizedSliceInclusion n)).mp
  rw [Category.assoc, cyclicHomNormalizedSlicePoint_inclusion,
    cyclicHomNormalizedSlicePoint_inclusion]
  exact cyclicHomNormalizedPoint_natural n f k

/-- The actual full normalization morphism with every original cyclic label retained. -/
def cyclicHomNormalizationMorphism :
    (cyclicHomAuxiliaryScheme n).left ⟶ cyclicHomNormalizedSlice n :=
  cyclicHomNormalizedSlicePoint n (𝟙 _)

/-- The constructed morphism represents normalization on every source scheme. -/
theorem cyclicHomNormalizationMorphism_comp (f : T ⟶ (cyclicHomAuxiliaryScheme n).left) :
    f ≫ cyclicHomNormalizationMorphism n = cyclicHomNormalizedSlicePoint n f := by
  have h := cyclicHomNormalizedSlicePoint_natural n (𝟙 _) f
  rw [Category.comp_id] at h
  exact h.symm

/-- The actual full closed inclusion admits the constructed normalization as a retraction. -/
@[reassoc] theorem cyclicHomNormalizedSliceInclusion_normalization :
    cyclicHomNormalizedSliceInclusion n ≫ cyclicHomNormalizationMorphism n =
      𝟙 (cyclicHomNormalizedSlice n) := by
  rw [cyclicHomNormalizationMorphism_comp]
  simpa only [Category.id_comp] using
    cyclicHomNormalizedSlicePoint_restrict n (𝟙 (cyclicHomNormalizedSlice n))

end FLT.Mazur.OddWeierstrassParameter
