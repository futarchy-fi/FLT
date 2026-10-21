/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeFlatVanishingOpen
public import FLT.Mazur.SchemeScalarPrincipalNeighborhood
public import FLT.Mazur.SchemeImageClosureFlatBaseChange

/-!
# Original scalar neighborhoods from vanishing on a flat branch

The equations are tested on the full Cartesian arrow pullback over a branch
neighborhood. Flat stalk descent and openness of the scalar change produce
an original principal neighborhood. One point of a fiber cannot replace the
whole inverse image of the branch neighborhood.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.SchemeScalarPrincipalNeighborhood
open SchemeAdicVanishingNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] {X Y : Scheme} (s : R →+* Γ(X, ⊤))
  (g : Y ⟶ Spec (.of R)) [Flat g] [LocallyOfFinitePresentation g]
local notation "π" => scalarMorphism s
local notation "k" => pullback.fst π g
local notation "h" => pullback.snd π g

/-- The bad-image closure of actual zero germs commutes with flat scalar branch change. -/
theorem flat_vanishing_bad_image (a : Γ(X, ⊤)) :
    closure (h '' (vanishingOpen ((k).appTop a) : Set (pullback π g : Scheme))ᶜ) =
      g ⁻¹' closure (π '' (vanishingOpen a : Set X)ᶜ) := by
  rw [flat_vanishingOpen_preimage]
  exact SchemeImageClosure.flat_pullback_image_closure π g (vanishingOpen a : Set X)ᶜ

/-- Equations on a full branch neighborhood exclude the original bad-image closure. -/
theorem mem_scalarNeighborhood_of_flat_vanishing (a : Γ(X, ⊤))
    (V : Y.Opens) (y : Y) (hy : y ∈ V)
    (hV : (pullback π g : Scheme).presheaf.map
      (homOfLE le_top : h ⁻¹ᵁ V ⟶ ⊤).op ((k).appTop a) = 0) :
    g y ∈ scalarNeighborhoodLocus s (vanishingOpen a) := by
  apply SchemeImageClosure.not_mem_closure_of_flat_neighborhood π g
    (vanishingOpen a : Set X)ᶜ V y hy
  intro z hz hn
  exact hn ((flat_germ_appTop_eq_zero_iff k a z).mp
    (le_vanishingOpen _ (h ⁻¹ᵁ V) hV hz))

/-- A branch solution constructs an original scalar denominator, with no closed-map assumption. -/
theorem exists_scalar_of_flat_vanishing (a : Γ(X, ⊤))
    (V : Y.Opens) (y : Y) (hy : y ∈ V)
    (hV : (pullback π g : Scheme).presheaf.map
      (homOfLE le_top : h ⁻¹ᵁ V ⟶ ⊤).op ((k).appTop a) = 0) :
    ∃ r : R, r ∉ (g y).asIdeal ∧ X.basicOpen (s r) ≤ vanishingOpen a :=
  (mem_scalarNeighborhoodLocus_iff s _ (g y)).mp
    (mem_scalarNeighborhood_of_flat_vanishing s g a V y hy hV)

end FLT.Mazur.SchemeScalarPrincipalNeighborhood
