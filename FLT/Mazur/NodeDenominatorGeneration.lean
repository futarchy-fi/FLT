/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalLocalizationGeneration
public import FLT.Mazur.PolygonNodePresentation

/-!
# Generation criteria for the exact localized node rings

The split node uses its two branch coordinates. The one-gon uses its conductor
and its first conductor monomial. In both cases the chosen denominator's
inverse is a separate, necessary image condition.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Polynomial

namespace FLT.Mazur.NodeDenominatorGeneration

open PolygonNodeEqualizer PolygonNodeLocalization PolygonNodePresentation
open PrincipalLocalizationGeneration
variable {K S : Type*} [CommRing K] [CommRing S] [Algebra K S]

/-- The two conductor generators generate B internally, not just its image in K[X]. -/
lemma one_adjoin : Algebra.adjoin K ({u, v} : Set (B (R := K))) = ⊤ := by
  apply Subalgebra.map_injective (f := (B (R := K)).val) Subtype.val_injective
  rw [← Algebra.adjoin_image, Algebra.map_top, Subalgebra.range_val]
  simpa only [Set.image_insert_eq, Set.image_singleton, Subalgebra.val_apply] using
    (b_adjoin (R := K))

/-- A map onto both node coordinates and the denominator inverse is surjective. -/
lemma split_surjective (s : A (R := K)) (f : S →ₐ[K] Localization.Away s)
    (hx : algebraMap (A (R := K)) (Localization.Away s) x ∈ f.range)
    (hy : algebraMap (A (R := K)) (Localization.Away s) y ∈ f.range)
    (hi : IsLocalization.Away.invSelf s ∈ f.range) : Function.Surjective f := by
  apply surjective_of_generators s {x, y} a_adjoin f _ hi
  intro g hg
  rcases hg with rfl | hg
  · exact hx
  · rcases hg with rfl
    exact hy

/-- The self-pinched node requires both conductor generators and the actual inverse. -/
lemma one_surjective (s : B (R := K)) (f : S →ₐ[K] Localization.Away s)
    (hu : algebraMap (B (R := K)) (Localization.Away s) u ∈ f.range)
    (hv : algebraMap (B (R := K)) (Localization.Away s) v ∈ f.range)
    (hi : IsLocalization.Away.invSelf s ∈ f.range) : Function.Surjective f := by
  apply surjective_of_generators s {u, v} one_adjoin f _ hi
  intro g hg
  rcases hg with rfl | hg
  · exact hu
  · rcases hg with rfl
    exact hv

end FLT.Mazur.NodeDenominatorGeneration
