/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SurjectiveDominantEpi
public import Mathlib.AlgebraicGeometry.Restrict

/-!
# Cancelling a surjective map to a reduced scheme in an isomorphism

A quasi-compact surjective map to a reduced scheme is a schematic epimorphism.
If its composite is an isomorphism, the second map is an isomorphism too.
The same argument applies over any target open, preserving its full inverse image.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.ReducedSurjectiveIsoCancellation
universe u
variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
  [Surjective f] [QuasiCompact f] [IsReduced Y]

/-- Schematic cancellation constructs the inverse of the second map. -/
theorem isIso_right [IsIso (f ≫ g)] : IsIso g := by
  let _ : IsSchemeTheoreticallyDominant f := .of_isDominant f
  let _ := SurjectiveDominantEpi.epi f
  refine ⟨⟨inv (f ≫ g) ≫ f, ?_, ?_⟩⟩
  · apply (cancel_epi f).mp
    rw [← Category.assoc f g, IsIso.hom_inv_id_assoc, Category.comp_id]
  · rw [Category.assoc, IsIso.inv_hom_id]

/-- An unchanged target open descends through the actual surjective contraction. -/
theorem isIso_restrict (U : Z.Opens) [hfg : IsIso ((f ≫ g) ∣_ U)] :
    IsIso (g ∣_ U) := by
  let _ : Surjective (f ∣_ (g ⁻¹ᵁ U)) :=
    IsZariskiLocalAtTarget.restrict (inferInstance : Surjective f) _
  let _ : IsIso (f ∣_ (g ⁻¹ᵁ U) ≫ g ∣_ U) := by
    rw [← morphismRestrict_comp f g U]
    exact hfg
  exact isIso_right (f ∣_ (g ⁻¹ᵁ U)) (g ∣_ U)

end FLT.Mazur.ReducedSurjectiveIsoCancellation
