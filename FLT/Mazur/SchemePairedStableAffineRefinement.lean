/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteGroupClosedEnvelopeRefinement

/-!
# Paired affine lifts inside a prescribed stable open

Both finite orbits lie in a common affine chart contained in the prescribed
open. Actual coefficient neighborhoods lift both maps and retain the open
bound, allowing original local scalar maps to be used on the new chart.
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

variable (O : X.Opens) (hO : ∀ g : G, (ρ g).hom ⁻¹ᵁ O = O)
include j k hO

/-- Both points, regardless of whether they are related, share a stable affine source chart. -/
theorem exists_common_chart_within (x y : X) (hxO : x ∈ O) (hyO : y ∈ O) :
    ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧ y ∈ U ∧ U ≤ O ∧
      ∀ g : G, (ρ g).hom ⁻¹ᵁ U = U := by
  let s := Set.range (fun g : G ↦ (ρ g).hom x) ∪
    Set.range (fun g : G ↦ (ρ g).hom y)
  have hs : s.Finite := (Set.finite_range _).union (Set.finite_range _)
  have hi (g : G) : (ρ g).hom '' s ⊆ s := by
    rintro _ ⟨z, hz, rfl⟩
    rcases hz with ⟨h, rfl⟩ | ⟨h, rfl⟩
    · exact Or.inl ⟨g * h, (action_mul_apply ρ g h x).symm⟩
    · exact Or.inr ⟨g * h, (action_mul_apply ρ g h y).symm⟩
  have hsO : s ⊆ O := by
    rintro z (⟨g, rfl⟩ | ⟨g, rfl⟩)
    · change x ∈ (ρ g).hom ⁻¹ᵁ O
      rwa [hO]
    · change y ∈ (ρ g).hom ⁻¹ᵁ O
      rwa [hO]
  obtain ⟨U, hU, hsU, hUO, he⟩ :=
    exists_closed_envelope_affine_refinement ρ j k s hs hi O hsO
  have hx : x ∈ s := Or.inl ⟨1, by change (ρ 1).hom x = x; rw [map_one]; rfl⟩
  have hy : y ∈ s := Or.inr ⟨1, by change (ρ 1).hom y = y; rw [map_one]; rfl⟩
  exact ⟨U, hU, hsU hx, hsU hy, hUO, he⟩

/-- Actual affine coefficient neighborhoods carry both original morphisms into one chart. -/
theorem exists_common_affine_lifts_within (u v : T ⟶ X) (t : T)
    (huO : u t ∈ O) (hvO : v t ∈ O) :
    ∃ (U : X.Opens) (W : T.Opens), IsAffineOpen U ∧ IsAffineOpen W ∧ t ∈ W ∧ U ≤ O ∧
      (∀ g : G, (ρ g).hom ⁻¹ᵁ U = U) ∧
      ∃ a b : W.toScheme ⟶ U.toScheme,
        a ≫ U.ι = W.ι ≫ u ∧ b ≫ U.ι = W.ι ≫ v := by
  obtain ⟨U, hU, hu, hv, hUO, he⟩ :=
    exists_common_chart_within ρ j k O hO (u t) (v t) huO hvO
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
  exact ⟨U, W, hU, hW, htW, hUO, he,
    IsOpenImmersion.lift U.ι (W.ι ≫ u) ha,
    IsOpenImmersion.lift U.ι (W.ι ≫ v) hb,
    IsOpenImmersion.lift_fac U.ι (W.ι ≫ u) ha,
    IsOpenImmersion.lift_fac U.ι (W.ι ≫ v) hb⟩

end FLT.Mazur.SchemePairedStableAffineLifts
