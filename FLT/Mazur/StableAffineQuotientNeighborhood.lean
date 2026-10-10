/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.StableAffineQuotientOverlap

/-!
# Stable affine refinement inside invariant opens

Invariant principal neighborhoods in an existing affine chart give smaller
stable affine charts inside any prescribed invariant open. Consequently an
invariant map can locally be restricted to an affine target neighborhood.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.SchemeFiniteGroupQuotient

namespace FLT.Mazur.StableAffineQuotient

universe u
variable {G : Type u} [Group G] [Finite G] {X : Scheme.{u}} (ρ : G →* Aut X)

/-- Invariant opens have stable affine refinements within every existing stable affine chart. -/
theorem exists_chart_subset (U : Chart ρ) (O : X.Opens)
    (hO : ∀ g : G, (ρ g).hom ⁻¹ᵁ O = O) (x : X) (hxU : x ∈ U.val) (hxO : x ∈ O) :
    ∃ W : Chart ρ, x ∈ W.val ∧ W.val ≤ O := by
  let x' : U.val.toScheme := ⟨x, hxU⟩
  have hs (g : G) (y : U.val.toScheme) (hy : y ∈ U.val.ι ⁻¹ᵁ O) :
      (action ρ U g).hom y ∈ U.val.ι ⁻¹ᵁ O := by
    change ((action ρ U g).hom y).val ∈ O
    rw [action_apply]
    change y.val ∈ (ρ g).hom ⁻¹ᵁ O
    rwa [hO]
  obtain ⟨r, hrx, hrO⟩ := exists_invariant_principal (action ρ U) (U.val.ι ⁻¹ᵁ O)
    hs x' hxO
  let B := U.val.toScheme.basicOpen (r : Γ(U.val.toScheme, ⊤))
  let W := U.val.ι ''ᵁ B
  have hforward (g : G) (z : X) (hz : z ∈ W) : (ρ g).hom z ∈ W := by
    obtain ⟨y, hy, rfl⟩ := hz
    refine ⟨(action ρ U g).hom y, ?_, action_apply ρ U g y⟩
    change y ∈ (action ρ U g).hom ⁻¹ᵁ B
    rwa [basicOpen_stable]
  have hW (g : G) : (ρ g).hom ⁻¹ᵁ W = W := by
    ext z
    change (ρ g).hom z ∈ W ↔ z ∈ W
    refine ⟨fun hz ↦ ?_, hforward g z⟩
    have hz' := hforward g⁻¹ ((ρ g).hom z) hz
    have he : (ρ g⁻¹).hom ((ρ g).hom z) = z := by
      change (ρ g⁻¹ * ρ g).hom z = z
      rw [← map_mul, inv_mul_cancel, map_one]
      rfl
    rwa [he] at hz'
  refine ⟨⟨W, ?_, hW⟩, ⟨x', hrx, rfl⟩, ?_⟩
  · exact (isAffineOpen_top U.val.toScheme).basicOpen _ |>.image_of_isOpenImmersion U.val.ι
  · rintro z ⟨y, hy, rfl⟩
    exact hrO hy

/-- Stable affine source charts can be chosen to map into affine target neighborhoods. -/
theorem exists_chart_affine_target {Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : ∀ g : G, (ρ g).hom ≫ f = f) (U : Chart ρ) (x : X) (hx : x ∈ U.val) :
    ∃ (W : Chart ρ) (V : Y.Opens),
      x ∈ W.val ∧ IsAffineOpen V ∧ W.val ≤ f ⁻¹ᵁ V := by
  obtain ⟨V, hV, hxV, _⟩ := exists_isAffineOpen_mem_and_subset
    (show f x ∈ (⊤ : Y.Opens) from trivial)
  have hO (g : G) : (ρ g).hom ⁻¹ᵁ (f ⁻¹ᵁ V) = f ⁻¹ᵁ V := by
    change ((ρ g).hom ≫ f) ⁻¹ᵁ V = _
    rw [hf]
  obtain ⟨W, hxW, hW⟩ := exists_chart_subset ρ U (f ⁻¹ᵁ V) hO x hx hxV
  exact ⟨W, V, hxW, hV, hW⟩

end FLT.Mazur.StableAffineQuotient
