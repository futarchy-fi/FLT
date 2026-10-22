/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteGroupClosedEnvelopeRefinement

/-!
# Independent stable affine targets over a common coefficient neighborhood

The two actions and ambient schemes may differ. Each endpoint retains its
prescribed stable domain, and both morphisms survive on one affine coefficient
neighborhood. This applies to normalized frames of unequal sizes.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.SchemeIndependentStableAffineLifts
open FiniteGroupNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {G H : Type} [Group G] [Finite G] [Group H] [Finite H]
  {X Y Z X' Y' Z' T : Scheme}
  (ρ : G →* Aut X) (τ : H →* Aut X')
  (j : X ⟶ Y) [IsClosedImmersion j] (k : Y ⟶ Z) [IsOpenImmersion k] [IsAffine Z]
  (j' : X' ⟶ Y') [IsClosedImmersion j'] (k' : Y' ⟶ Z') [IsOpenImmersion k']
  [IsAffine Z'] (O : X.Opens) (O' : X'.Opens)
  (hO : ∀ g : G, (ρ g).hom ⁻¹ᵁ O = O) (hO' : ∀ g : H, (τ g).hom ⁻¹ᵁ O' = O')

include j k j' k' hO hO' in
/-- Both independently constructed stable charts retain the full coefficient morphisms. -/
theorem exists_affine_lifts (u : T ⟶ X) (v : T ⟶ X') (t : T)
    (hu : u t ∈ O) (hv : v t ∈ O') :
    ∃ (U : X.Opens) (V : X'.Opens) (W : T.Opens),
      IsAffineOpen U ∧ IsAffineOpen V ∧ IsAffineOpen W ∧ t ∈ W ∧ U ≤ O ∧ V ≤ O' ∧
      (∀ g : G, (ρ g).hom ⁻¹ᵁ U = U) ∧ (∀ g : H, (τ g).hom ⁻¹ᵁ V = V) ∧
      ∃ (a : W.toScheme ⟶ U.toScheme) (b : W.toScheme ⟶ V.toScheme),
        a ≫ U.ι = W.ι ≫ u ∧ b ≫ V.ι = W.ι ≫ v := by
  obtain ⟨U, hU, huU, hUO, hρ⟩ :=
    exists_closed_envelope_affine_basis ρ j k O hO (u t) hu
  obtain ⟨V, hV, hvV, hVO, hτ⟩ :=
    exists_closed_envelope_affine_basis τ j' k' O' hO' (v t) hv
  have ht : t ∈ u ⁻¹ᵁ U ⊓ v ⁻¹ᵁ V := ⟨huU, hvV⟩
  obtain ⟨W, hW, htW, hWV⟩ := exists_isAffineOpen_mem_and_subset ht
  have ha : Set.range (W.ι ≫ u) ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, rfl⟩
    exact (hWV z.property).1
  have hb : Set.range (W.ι ≫ v) ⊆ Set.range V.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, rfl⟩
    exact (hWV z.property).2
  exact ⟨U, V, W, hU, hV, hW, htW, hUO, hVO, hρ, hτ,
    IsOpenImmersion.lift U.ι (W.ι ≫ u) ha,
    IsOpenImmersion.lift V.ι (W.ι ≫ v) hb,
    IsOpenImmersion.lift_fac U.ι (W.ι ≫ u) ha,
    IsOpenImmersion.lift_fac V.ι (W.ι ≫ v) hb⟩

end FLT.Mazur.SchemeIndependentStableAffineLifts
