/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.AlgebraicGeometry.OpenImmersion

/-!
# Ranges inside specified open subschemes

Keep range calculations abstract in the original morphisms, so restricting
large glued models does not unfold their construction during reduction.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.OpenRangeRestriction
universe u
variable {X Y U V A B : Scheme.{u}}

/-- An open inclusion detects the entire range of a specified lifted map. -/
theorem preimage_range (i : U ⟶ X) [IsOpenImmersion i]
    (a : A ⟶ U) (b : A ⟶ X) (h : a ≫ i = b) :
    i ⁻¹' Set.range b = Set.range a := by
  rw [← h]
  change i ⁻¹' Set.range (i ∘ a) = _
  rw [Set.range_comp, Set.preimage_image_eq _ i.isOpenEmbedding.injective]

/-- A saturated pair of full ranges remains saturated after restriction to open subschemes. -/
theorem preimage_range_map (p : Y ⟶ X) (q : V ⟶ U)
    (i : U ⟶ X) (j : V ⟶ Y) [IsOpenImmersion i] [IsOpenImmersion j]
    (a : A ⟶ U) (b : A ⟶ X) (a' : B ⟶ V) (b' : B ⟶ Y)
    (h : q ≫ i = j ≫ p) (ha : a ≫ i = b) (hb : a' ≫ j = b')
    (hp : p ⁻¹' Set.range b = Set.range b') : q ⁻¹' Set.range a = Set.range a' := by
  rw [← preimage_range i a b ha, ← preimage_range j a' b' hb]
  change (q ≫ i) ⁻¹' Set.range b = _
  rw [h]
  change j ⁻¹' (p ⁻¹' Set.range b) = _
  rw [hp]

end FLT.Mazur.OpenRangeRestriction
