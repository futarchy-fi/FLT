/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ClassifiedGenusOneFamily

/-!
# Classified genus-one families on specified cartesian squares

Pasting with a chosen base-change square retains the actual structure map on
every geometric fiber. No choice of a canonical pullback object is required.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.FCurve

open CurveFiberHypotheses DRFiberClassification

variable {X S T Y : Scheme} {f : X ⟶ S} {g : T ⟶ S}
  {p : Y ⟶ X} {q : Y ⟶ T}

/-- Any specified cartesian square retains the entire classified genus-one contract. -/
theorem ClassifiedGenusOneFamily.of_isPullback (hf : ClassifiedGenusOneFamily f)
    (h : IsPullback p q f g) : ClassifiedGenusOneFamily q := by
  let _ : IsProper f := hf.family.1
  let _ : IsProper q := MorphismProperty.of_isPullback h inferInstance
  have hfamily : ProperFlatFamily q :=
    ⟨inferInstance, MorphismProperty.of_isPullback h hf.family.2.1,
      MorphismProperty.of_isPullback h hf.family.2.2⟩
  refine ⟨hfamily, ⟨?_⟩, ⟨?_⟩⟩
  · intro L _ _ s Z a b hs
    exact hf.classified.fiber L (s ≫ g) (a ≫ p) b (hs.paste_horiz h)
  · intro L _ _ s Z a b hs
    exact hf.genus.fiber L (s ≫ g) (a ≫ p) b (hs.paste_horiz h)

/-- Isomorphisms over the base preserve the classified genus-one family itself. -/
theorem ClassifiedGenusOneFamily.of_overIso {X Y : Over S}
    (hf : ClassifiedGenusOneFamily X.hom) (e : X ≅ Y) :
    ClassifiedGenusOneFamily Y.hom := by
  have hp : IsPullback e.inv.left Y.hom X.hom (𝟙 S) :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  exact hf.of_isPullback hp

end FLT.Mazur.FCurve
