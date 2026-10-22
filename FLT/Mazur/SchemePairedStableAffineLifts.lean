/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteGroupClosedEnvelopeNeighborhood

/-!
# Two independent scheme tests lift to a common stable affine chart

A closed subscheme of an affine open has a common stable affine neighborhood
of both finite orbits. Restricting the coefficient scheme to an affine open
then constructs both lifts, preserving exact scheme maps and nilpotents.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.SchemePairedStableAffineLifts
open FiniteGroupNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {G : Type} [Group G] [Finite G] {X Y Z T : Scheme}
  (ρ : G →* Aut X) (j : X ⟶ Y) [IsClosedImmersion j]
  (k : Y ⟶ Z) [IsOpenImmersion k] [IsAffine Z]

include j k

/-- Both points, regardless of whether they are related, share a stable affine source chart. -/
theorem exists_common_chart (x y : X) :
    ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧ y ∈ U ∧
      ∀ g : G, (ρ g).hom ⁻¹ᵁ U = U := by
  let s := Set.range (fun g : G ↦ (ρ g).hom x) ∪
    Set.range (fun g : G ↦ (ρ g).hom y)
  have hs : s.Finite := (Set.finite_range _).union (Set.finite_range _)
  have hi (g : G) : (ρ g).hom '' s ⊆ s := by
    rintro _ ⟨z, hz, rfl⟩
    rcases hz with ⟨h, rfl⟩ | ⟨h, rfl⟩
    · exact Or.inl ⟨g * h, (action_mul_apply ρ g h x).symm⟩
    · exact Or.inr ⟨g * h, (action_mul_apply ρ g h y).symm⟩
  obtain ⟨U, hU, hsU, he⟩ := exists_closed_envelope_stable_affine ρ j k s hs hi
  have hx : x ∈ s := Or.inl ⟨1, by change (ρ 1).hom x = x; rw [map_one]; rfl⟩
  have hy : y ∈ s := Or.inr ⟨1, by change (ρ 1).hom y = y; rw [map_one]; rfl⟩
  exact ⟨U, hU, hsU hx, hsU hy, he⟩

/-- Actual affine coefficient neighborhoods carry both original morphisms into one chart. -/
theorem exists_common_affine_lifts (u v : T ⟶ X) (t : T) :
    ∃ (U : X.Opens) (W : T.Opens), IsAffineOpen U ∧ IsAffineOpen W ∧ t ∈ W ∧
      (∀ g : G, (ρ g).hom ⁻¹ᵁ U = U) ∧
      ∃ a b : W.toScheme ⟶ U.toScheme,
        a ≫ U.ι = W.ι ≫ u ∧ b ≫ U.ι = W.ι ≫ v := by
  obtain ⟨U, hU, hu, hv, he⟩ := exists_common_chart ρ j k (u t) (v t)
  have ht : t ∈ u ⁻¹ᵁ U ⊓ v ⁻¹ᵁ U := ⟨hu, hv⟩
  obtain ⟨W, hW, htW, hWU⟩ := exists_isAffineOpen_mem_and_subset ht
  have ha : Set.range (W.ι ≫ u) ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, rfl⟩
    exact (hWU z.property).1
  have hb : Set.range (W.ι ≫ v) ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, rfl⟩
    exact (hWU z.property).2
  exact ⟨U, W, hU, hW, htW, he,
    IsOpenImmersion.lift U.ι (W.ι ≫ u) ha,
    IsOpenImmersion.lift U.ι (W.ι ≫ v) hb,
    IsOpenImmersion.lift_fac U.ι (W.ι ≫ u) ha,
    IsOpenImmersion.lift_fac U.ι (W.ι ≫ v) hb⟩

end FLT.Mazur.SchemePairedStableAffineLifts
