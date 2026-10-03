/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCyclicNormalizationFinite
public import FLT.Mazur.OneGonNormalizationFinite
public import FLT.Mazur.PolygonCoconeComparison
/-!
# Finite surjective normalization of every positive polygon

Combine the one-gon and cyclic computations, then transport the result
to any supplied pinching cocone through the canonical comparison.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
namespace FLT.Mazur.PolygonNormalizationFinite
variable (K : Type u) [Field K]

/-- The one-component coproduct normalization is finite. -/
instance oneGonOver_finite : IsFinite (OneGonNormalization.normalizationOver K).left := by
  let e := (Over.forget (Spec (.of K))).mapIso
    (coproductUniqueIso (fun _ : Fin 1 ↦ PolygonPinching.component K)).symm
  rw [← MorphismProperty.cancel_left_of_respectsIso (P := @IsFinite) e.hom]
  change IsFinite (PolygonPinching.componentι K 1 0 ≫
    OneGonNormalization.normalizationOver K).left
  rw [OneGonNormalization.componentι_normalizationOver]
  exact OneGonNormalizationFinite.normalization_finite K

/-- The one-component coproduct normalization is surjective. -/
theorem oneGonOver_surjective :
    Function.Surjective (OneGonNormalization.normalizationOver K).left := by
  intro y
  obtain ⟨x, hx⟩ := OneGonNormalizationFinite.normalization_surjective K y
  refine ⟨(PolygonPinching.componentι K 1 0).left x, ?_⟩
  have h := congrArg (fun f ↦ f.left x) (OneGonNormalization.componentι_normalizationOver K 0)
  exact h.trans hx

/-- The specified normalization of every positive polygon is finite. -/
instance normalization_finite (n : ℕ) [NeZero n] :
    IsFinite (PolygonAtlas.normalization K n).left := by
  rcases n with _ | (_ | n)
  · exact (NeZero.ne 0 rfl).elim
  · exact oneGonOver_finite K
  · exact PolygonCyclicNormalizationFinite.specified_finite K (n + 2) (by omega)

/-- The specified normalization of every positive polygon is surjective. -/
theorem normalization_surjective (n : ℕ) [NeZero n] :
    Function.Surjective (PolygonAtlas.normalization K n).left := by
  rcases n with _ | (_ | n)
  · exact (NeZero.ne 0 rfl).elim
  · exact oneGonOver_surjective K
  · exact PolygonCyclicNormalizationFinite.specified_surjective K (n + 2) (by omega)

variable (n : ℕ) [NeZero n] (hn : 0 < n) {C : Over (Spec (.of K))}
  (p : PolygonPinching.components K n ⟶ C) (q : PolygonPinching.nodes K n ⟶ C)
  (h : IsPushout (PolygonPinching.toComponents K n hn) (PolygonPinching.toNodes K n) p q)

include h in
/-- Any cocone with the specified pinching pushout has finite normalization. -/
theorem cocone_normalization_finite : IsFinite p.left := by
  have : IsIso (PolygonPinching.polygonIso K n hn p q h).hom.left :=
    inferInstanceAs (IsIso ((Over.forget _).map (PolygonPinching.polygonIso K n hn p q h).hom))
  rw [← PolygonPinching.normalization_polygonIso K n hn p q h]
  change IsFinite ((PolygonAtlas.normalization K n).left ≫ _)
  infer_instance

include h in
/-- Any cocone with the specified pinching pushout has surjective normalization. -/
theorem cocone_normalization_surjective : Function.Surjective p.left := by
  have hIso : Function.Surjective (PolygonPinching.polygonIso K n hn p q h).hom.left := by
    intro y
    exact ⟨(PolygonPinching.polygonIso K n hn p q h).inv.left y,
      congrArg (fun f ↦ f.left y) (PolygonPinching.polygonIso K n hn p q h).inv_hom_id⟩
  intro y
  obtain ⟨z, rfl⟩ := hIso y
  obtain ⟨x, hx⟩ := normalization_surjective K n z
  refine ⟨x, ?_⟩
  conv_lhs => rw [← PolygonPinching.normalization_polygonIso K n hn p q h]
  change (PolygonPinching.polygonIso K n hn p q h).hom.left
    ((PolygonAtlas.normalization K n).left x) = _
  rw [hx]
end FLT.Mazur.PolygonNormalizationFinite
