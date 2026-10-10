/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OpenIntersectionProduct
public import FLT.Mazur.SeparatedOverlapClosedComparison

/-!
# Cancelling closed chart refinements in overlap products

Closedness into an older chart product implies closedness into the refined
product, retaining the exact inverse-image opens and the original base.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.Approximation

universe u

/-- A closed refinement cancels from the product map of a pulled-back intersection. -/
theorem isClosedImmersion_openIntersectionProduct_of_restrict
    {X Y S : Scheme.{u}} (q : X ⟶ Y) [IsClosedImmersion q]
    (f : Y ⟶ S) (U V : Y.Opens)
    (h : IsClosedImmersion ((q ∣_ (U ⊓ V)) ≫ openIntersectionProduct f U V)) :
    IsClosedImmersion (openIntersectionProduct (q ≫ f) (q ⁻¹ᵁ U) (q ⁻¹ᵁ V)) := by
  let A := q ⁻¹ᵁ U
  let B := q ⁻¹ᵁ V
  let e := X.isoOfEq (q.preimage_inf (U := U) (V := V))
  have hr : A.ι ≫ (q ≫ f) = (q ∣_ U) ≫ (U.ι ≫ f) := by
    simp only [A, ← Category.assoc, morphismRestrict_ι]
  have hs : B.ι ≫ (q ≫ f) = (q ∣_ V) ≫ (V.ι ≫ f) := by
    simp only [B, ← Category.assoc, morphismRestrict_ι]
  let t := pullback.map (A.ι ≫ q ≫ f) (B.ι ≫ q ≫ f) (U.ι ≫ f) (V.ι ≫ f)
    (q ∣_ U) (q ∣_ V) (𝟙 S)
    ((Category.comp_id _).trans hr) ((Category.comp_id _).trans hs)
  let _ : MorphismProperty.IsStableUnderComposition @IsClosedImmersion.{u} :=
    ⟨fun a b ha hb ↦ @IsClosedImmersion.comp _ _ _ a b ha hb⟩
  let _ : IsClosedImmersion t := MorphismProperty.pullbackMap (P := @IsClosedImmersion)
    (inferInstance : IsClosedImmersion (q ∣_ U))
    (inferInstance : IsClosedImmersion (q ∣_ V)) hr hs
  have he : openIntersectionProduct (q ≫ f) A B ≫ t =
      e.inv ≫ (q ∣_ (U ⊓ V)) ≫ openIntersectionProduct f U V := by
    apply pullback.hom_ext
    · apply (cancel_mono U.ι).mp
      simp [t, e, A, B]
    · apply (cancel_mono V.ι).mp
      simp [t, e, A, B]
  let _ : IsClosedImmersion ((q ∣_ (U ⊓ V)) ≫ openIntersectionProduct f U V) := h
  let _ : IsClosedImmersion (openIntersectionProduct (q ≫ f) A B ≫ t) :=
    he.symm ▸ inferInstance
  exact IsClosedImmersion.of_comp_isClosedImmersion _ t

end FLT.Mazur.Approximation
