/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SeparatedOverlapPullback

/-!
# Closed overlap maps into enlarged chart products

An overlap of a separated scheme maps by a closed immersion to its chart
product. Closed embeddings of both charts into larger charts preserve this
closedness, with the same base scheme and specified structural maps.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.Approximation

universe u

/-- Closed chart embeddings carry a separated overlap to a closed product map. -/
theorem isClosedImmersion_overlap_comparison
    {X S A B W A' B' : Scheme.{u}} (f : X ⟶ S) [IsSeparated f]
    (i : A ⟶ X) (j : B ⟶ X) (a : W ⟶ A) (b : W ⟶ B)
    (hp : IsPullback a b i j) (p : A' ⟶ S) (q : B' ⟶ S)
    (r : A ⟶ A') (s : B ⟶ B') [IsClosedImmersion r] [IsClosedImmersion s]
    (hr : i ≫ f = r ≫ p) (hs : j ≫ f = s ≫ q) :
    IsClosedImmersion (pullback.lift (f := p) (g := q) (a ≫ r) (b ≫ s) (by
      rw [Category.assoc, ← hr, ← Category.assoc, hp.w,
        Category.assoc, hs, ← Category.assoc])) := by
  let _ : MorphismProperty.IsStableUnderComposition @IsClosedImmersion.{u} :=
    ⟨fun a b ha hb ↦ @IsClosedImmersion.comp _ _ _ a b ha hb⟩
  let t := pullback.map (i ≫ f) (j ≫ f) p q r s (𝟙 S)
    ((Category.comp_id _).trans hr) ((Category.comp_id _).trans hs)
  let _ : IsClosedImmersion t :=
    MorphismProperty.pullbackMap (P := @IsClosedImmersion)
      (inferInstance : IsClosedImmersion r) (inferInstance : IsClosedImmersion s) hr hs
  have he : pullback.lift (f := p) (g := q) (a ≫ r) (b ≫ s) (by
        rw [Category.assoc, ← hr, ← Category.assoc, hp.w,
          Category.assoc, hs, ← Category.assoc]) =
      hp.isoPullback.hom ≫ pullback.mapDesc i j f ≫ t := by
    apply pullback.hom_ext <;> simp [t]
  exact (congrArg (fun z ↦ IsClosedImmersion z) he).mpr
    (inferInstanceAs (IsClosedImmersion (hp.isoPullback.hom ≫ pullback.mapDesc i j f ≫ t)))

end FLT.Mazur.Approximation
