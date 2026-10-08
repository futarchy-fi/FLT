/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSheafOpenImmersionTopSections
public import FLT.Mazur.SchemeModulePullbackOpenUnits

/-!
# Section maps under refinement of an open chart

The canonical image-section isomorphism respects further chart pullback.
Its compatibility uses the actual pullback unit and path comparison.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

universe u

namespace FLT.Mazur.ModuleSheafOpenImmersionSections

open SchemeModulePullbackUnits SheafPullbackPathComparison

variable {X Y Z : Scheme.{u}}

/-- On global sections the restricted unit is the ordinary unit. -/
lemma openUnit_top (f : X ⟶ Y) (M : Y.Modules) :
    openUnit f M ⊤ ⊤ le_rfl = ((pullbackPushforwardAdjunction f).unit.app M).app ⊤ := by
  unfold openUnit
  rw [show homOfLE (show (⊤ : X.Opens) ≤ f ⁻¹ᵁ ⊤ from le_rfl) = 𝟙 _ from rfl]
  rw [op_id]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]

/-- The image-section isomorphism is the restricted unit on the open range. -/
lemma topSectionsIso_eq_openUnit (i : Y ⟶ X) [IsOpenImmersion i] (M : X.Modules)
    (h : (⊤ : Y.Opens) ≤ i ⁻¹ᵁ i.opensRange) :
    (topSectionsIso i M).hom = openUnit i M i.opensRange ⊤ h := by
  rw [topSectionsIso_unit]
  unfold openUnit
  congr 2

/-- A refinement of an immersion has image contained in the ambient chart. -/
lemma refinement_opensRange_le (p : Z ⟶ Y) (i : Y ⟶ X) (r : Z ⟶ X)
    [IsOpenImmersion i] [IsOpenImmersion r] (e : p ≫ i = r) : r.opensRange ≤ i.opensRange := by
  rintro _ ⟨z, rfl⟩
  exact ⟨p z, congrArg (fun k ↦ k z) e⟩

/-- Restricting an ambient section and then pulling back agrees with the iterated chart unit. -/
lemma topSectionsIso_refine (p : Z ⟶ Y) (i : Y ⟶ X) (r : Z ⟶ X)
    [IsOpenImmersion i] [IsOpenImmersion r] (e : p ≫ i = r) (M : X.Modules) :
    M.presheaf.map (homOfLE (refinement_opensRange_le p i r e)).op ≫
        (topSectionsIso r M).hom =
      (topSectionsIso i M).hom ≫
        ((pullbackPushforwardAdjunction p).unit.app ((pullback i).obj M)).app ⊤ ≫
          ((comparison p i r e).hom.app M).app ⊤ := by
  have hi : (⊤ : Y.Opens) ≤ i ⁻¹ᵁ i.opensRange := by
    rw [Scheme.Hom.preimage_opensRange]
  have hr : (⊤ : Z.Opens) ≤ r ⁻¹ᵁ r.opensRange := by
    rw [Scheme.Hom.preimage_opensRange]
  rw [topSectionsIso_eq_openUnit r M hr, topSectionsIso_eq_openUnit i M hi,
    ← openUnit_top, openUnit_restrict]
  exact (openUnit_comparison p i r e M i.opensRange ⊤ ⊤ hi le_rfl _).symm

end FLT.Mazur.ModuleSheafOpenImmersionSections
