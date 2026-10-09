/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OpenIntersectionProduct
public import FLT.Mazur.SeparatedOverlapClosedComparison

/-!
# Closed overlap maps along a closed projection

A closed projection from a separated scheme makes the restriction of each
stage overlap-product map closed on the original scheme.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.Approximation

universe u

/-- Pulling a stage intersection back along a closed projection yields a closed product map. -/
theorem isClosedImmersion_restrict_openIntersectionProduct
    {X Y S : Scheme.{u}} (q : X ⟶ Y) [IsClosedImmersion q]
    (f : Y ⟶ S) [IsSeparated (q ≫ f)] (U V : Y.Opens) :
    IsClosedImmersion ((q ∣_ (U ⊓ V)) ≫ openIntersectionProduct f U V) := by
  let A := q ⁻¹ᵁ U
  let B := q ⁻¹ᵁ V
  let e := X.isoOfEq (q.preimage_inf (U := U) (V := V))
  let a : (A ⊓ B).toScheme ⟶ A.toScheme := X.homOfLE inf_le_left
  let b : (A ⊓ B).toScheme ⟶ B.toScheme := X.homOfLE inf_le_right
  have hr : A.ι ≫ (q ≫ f) = (q ∣_ U) ≫ (U.ι ≫ f) := by
    simp only [A, ← Category.assoc, morphismRestrict_ι]
  have hs : B.ι ≫ (q ≫ f) = (q ∣_ V) ≫ (V.ι ≫ f) := by
    simp only [B, ← Category.assoc, morphismRestrict_ι]
  let t := pullback.lift (f := U.ι ≫ f) (g := V.ι ≫ f)
    (a ≫ (q ∣_ U)) (b ≫ (q ∣_ V)) (by
      rw [Category.assoc, ← hr, ← Category.assoc, (isPullback_opens_inf A B).w,
        Category.assoc, hs, ← Category.assoc])
  let _ : IsClosedImmersion t := isClosedImmersion_overlap_comparison (q ≫ f)
    A.ι B.ι a b (isPullback_opens_inf A B) (U.ι ≫ f) (V.ι ≫ f)
    (q ∣_ U) (q ∣_ V) hr hs
  have he : e.inv ≫ (q ∣_ (U ⊓ V)) ≫ openIntersectionProduct f U V = t := by
    apply pullback.hom_ext
    · apply (cancel_mono U.ι).mp
      simp [t, a, e, A, B]
    · apply (cancel_mono V.ι).mp
      simp [t, b, e, A, B]
  apply (MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion e.inv _).mp
  exact he.symm ▸ inferInstance

end FLT.Mazur.Approximation
