/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassNormalizedSlice

/-!
# The normalized slice represents its equations on every test scheme

Use the global-sections adjunction only for the four equation functions.
The auxiliary point itself remains a morphism to the original level-four
scheme. No affineness of that scheme or of the test scheme is required.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FLT.Mazur.UniversalWeierstrass

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {T : Scheme}

/-- A normalized actual auxiliary family factors through the original closed slice. -/
def normalizedSliceFamilyLift (f : T ⟶ levelFour.left)
    (hn : SatisfiesNormalization f.appTop.hom) : T ⟶ normalizedSlice :=
  pullback.lift f
    (T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (normalizedSliceLift f.appTop.hom hn))) (by
      rw [Category.assoc, ← Spec.map_comp]
      exact Scheme.toSpecΓ_naturality f)

/-- Factoring through the slice keeps the whole original auxiliary family. -/
@[reassoc] theorem normalizedSliceFamilyLift_inclusion (f : T ⟶ levelFour.left)
    (hn : SatisfiesNormalization f.appTop.hom) :
    normalizedSliceFamilyLift f hn ≫ normalizedSliceInclusion = f := pullback.lift_fst ..

/-- Every family in the original closed slice satisfies its four actual frame equations. -/
theorem normalizedSliceFamily_satisfies (l : T ⟶ normalizedSlice) :
    SatisfiesNormalization (l ≫ normalizedSliceInclusion).appTop.hom := by
  let q := CommRingCat.ofHom normalizedSliceQuotient
  let k := l ≫ pullback.snd levelFour.left.toSpecΓ (Spec.map q)
  have hc : k ≫ Spec.map q = (l ≫ normalizedSliceInclusion) ≫ levelFour.left.toSpecΓ := by
    simp only [k, Category.assoc, ← pullback.condition]
    rfl
  have he : q ≫ (Scheme.ΓSpecIso (.of NormalizedSliceRing)).inv ≫ k.appTop =
      (l ≫ normalizedSliceInclusion).appTop := by
    rw [← Category.assoc, Scheme.ΓSpecIso_inv_naturality, Category.assoc,
      ← Scheme.Hom.comp_appTop, hc, Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop]
    exact (Scheme.ΓSpecIso (.of AuxiliarySectionRing)).inv_hom_id_assoc _
  intro i
  have hi := congrArg (fun f => f.hom (normalizedSliceRelation i)) he
  change _ = _ at hi
  rw [← hi]
  change k.appTop.hom ((Scheme.ΓSpecIso (.of NormalizedSliceRing)).inv.hom
    (normalizedSliceQuotient (normalizedSliceRelation i))) = 0
  rw [normalizedSliceQuotient_satisfies i, map_zero, map_zero]

/-- On every test scheme, the actual normalized slice represents the frame equations uniquely. -/
theorem normalizedSliceFamily_iff (f : T ⟶ levelFour.left) :
    SatisfiesNormalization f.appTop.hom ↔
      ∃! l : T ⟶ normalizedSlice, l ≫ normalizedSliceInclusion = f := by
  constructor
  · intro hn
    refine ⟨normalizedSliceFamilyLift f hn, normalizedSliceFamilyLift_inclusion f hn, ?_⟩
    intro l hl
    exact (cancel_mono normalizedSliceInclusion).mp
      (hl.trans (normalizedSliceFamilyLift_inclusion f hn).symm)
  · rintro ⟨l, rfl, _⟩
    exact normalizedSliceFamily_satisfies l

/-- The representation retains the full auxiliary morphism as its underlying point. -/
def normalizedSliceFamilyRepresentation :
    (T ⟶ normalizedSlice) ≃
      {f : T ⟶ levelFour.left // SatisfiesNormalization f.appTop.hom} where
  toFun l := ⟨l ≫ normalizedSliceInclusion, normalizedSliceFamily_satisfies l⟩
  invFun f := normalizedSliceFamilyLift f.val f.property
  left_inv l := (cancel_mono normalizedSliceInclusion).mp
    (normalizedSliceFamilyLift_inclusion (l ≫ normalizedSliceInclusion)
      (normalizedSliceFamily_satisfies l))
  right_inv f := Subtype.ext (normalizedSliceFamilyLift_inclusion f.val f.property)

/-- The underlying representing bijection commutes with every test-scheme morphism. -/
theorem normalizedSliceFamilyRepresentation_natural {U : Scheme} (a : U ⟶ T)
    (l : T ⟶ normalizedSlice) :
    (normalizedSliceFamilyRepresentation (a ≫ l)).val =
      a ≫ (normalizedSliceFamilyRepresentation l).val := Category.assoc ..

end FLT.Mazur.UniversalWeierstrass
