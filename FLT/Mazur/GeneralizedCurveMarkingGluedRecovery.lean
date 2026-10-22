/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveMarkingOpenGluing

/-!
# Cartesian recovery of the actual original affine cubic charts

The glued chart image is exactly the inverse image of its original base
open. Thus the original cubic, including singular fibers and nilpotents,
is the categorical base restriction of the constructed global scheme.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} [IsLocallyNoetherian S] (E : GeneralizedEllipticCurve S)
  (s : 𝟙_ (Over S) ⟶ E.group)

/-- A glued cubic chart occupies exactly its original affine base open. -/
theorem smoothMarkingGluedChart_range (i : SmoothMarkingAffineChart E s) :
    Set.range (smoothMarkingGluedChart E s i) =
      smoothMarkingGluedBase E s ⁻¹' (i.base.1 : Set S) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    change smoothMarkingGluedBase E s (smoothMarkingGluedChart E s i y) ∈ i.base.1
    rw [← Scheme.Hom.comp_apply, smoothMarkingGluedChart_base]
    exact smoothMarkingAffineBase_mem E s i y
  · intro hx
    obtain ⟨j, y, rfl⟩ := smoothMarkingGluedChart_jointly_surjective E s x
    change smoothMarkingGluedBase E s (smoothMarkingGluedChart E s j y) ∈ i.base.1 at hx
    rw [← Scheme.Hom.comp_apply, smoothMarkingGluedChart_base] at hx
    have hy : smoothMarkingAffineBase E s j y ∈ i.base.1 ⊓ j.base.1 :=
      ⟨hx, smoothMarkingAffineBase_mem E s j y⟩
    obtain ⟨l, hl, hle⟩ := exists_smoothMarkingAffineChart E s hy
    let fli : l ⟶ i := homOfLE (hle.trans inf_le_left)
    let flj : l ⟶ j := homOfLE (hle.trans inf_le_right)
    have hr : y ∈ Set.range ((smoothMarkingAffineDiagram E s).map flj) := by
      rw [smoothMarkingAffineDiagram_range]
      exact hl
    obtain ⟨z, hz⟩ := hr
    refine ⟨(smoothMarkingAffineDiagram E s).map fli z, ?_⟩
    rw [← hz, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply,
      smoothMarkingGluedChart_naturality, smoothMarkingGluedChart_naturality]

/-- The actual affine cubic chart is the categorical restriction of the global cubic. -/
theorem smoothMarkingGluedChart_isPullback (i : SmoothMarkingAffineChart E s) :
    IsPullback (smoothMarkingAffineStructure E s i) (smoothMarkingGluedChart E s i)
      i.base.1.ι (smoothMarkingGluedBase E s) := by
  apply IsOpenImmersion.isPullback _ _ _ _ (smoothMarkingGluedChart_base E s i)
  apply SetLike.coe_injective
  change smoothMarkingGluedBase E s ⁻¹' Set.range i.base.1.ι =
    Set.range (smoothMarkingGluedChart E s i)
  rw [Scheme.Opens.range_ι, smoothMarkingGluedChart_range]

end FLT.Mazur.GeneralizedEllipticCurve
