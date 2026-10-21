/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.AlgebraicGeometry.Restrict

/-!
# Comparing restricted outputs along equal full input maps

Equality of the full input morphisms identifies both the complete inverse
image domains and the output morphisms on those domains.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.SchemeRestrictedOutputComparison
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {X Y Z B T : Scheme.{u}} (f : X ⟶ Y) (g : X ⟶ Z)
  (a : Y ⟶ B) (b : Z ⟶ B) (h : f ≫ a = g ≫ b) (U : B.Opens)

include h in
/-- Equal full input morphisms have identical complete output domains. -/
theorem domain_eq : f ⁻¹ᵁ (a ⁻¹ᵁ U) = g ⁻¹ᵁ (b ⁻¹ᵁ U) := by
  rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, h]

/-- The equality of domains identifies the actual restricted input maps. -/
@[reassoc] theorem input_eq :
    X.homOfLE (domain_eq f g a b h U).le ≫ (g ∣_ b ⁻¹ᵁ U) ≫ (b ∣_ U) =
      (f ∣_ a ⁻¹ᵁ U) ≫ (a ∣_ U) := by
  apply (cancel_mono U.ι).mp
  simp only [Category.assoc, morphismRestrict_ι, morphismRestrict_ι_assoc,
    Scheme.homOfLE_ι_assoc]
  simpa only [Category.assoc] using
    congrArg (fun k => (f ⁻¹ᵁ (a ⁻¹ᵁ U)).ι ≫ k) h.symm

/-- Every constructed output agrees under the same canonical domain identification. -/
theorem output_eq (o : U.toScheme ⟶ T) :
    X.homOfLE (domain_eq f g a b h U).le ≫ (g ∣_ b ⁻¹ᵁ U) ≫ (b ∣_ U) ≫ o =
      (f ∣_ a ⁻¹ᵁ U) ≫ (a ∣_ U) ≫ o :=
  input_eq_assoc f g a b h U o

end FLT.Mazur.SchemeRestrictedOutputComparison
