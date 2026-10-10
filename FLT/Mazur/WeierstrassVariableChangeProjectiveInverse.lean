/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassVariableChangeLinear

/-!
# Inversion of the actual projective coordinate isomorphism

The inverse admissible change induces the inverse ambient scheme map.
-/

@[expose] public noncomputable section

open WeierstrassCurve CategoryTheory

namespace FLT.Mazur.WeierstrassVariableChangeLinear

variable {R : Type} [CommRing R] (C : VariableChange R)

/-- Inverting the admissible change inverts the constructed linear equivalence. -/
theorem linearEquiv_inv : linearEquiv C⁻¹ = (linearEquiv C).symm := by
  ext v
  rfl

/-- The ambient projective isomorphisms have the exact inverse law. -/
theorem projectiveIso_inv : projectiveIso C⁻¹ = (projectiveIso C).symm := by
  rw [projectiveIso, linearEquiv_inv, LinearEquiv.symm_symm]
  rfl

/-- The two successive ambient maps cancel. -/
@[reassoc] theorem projectiveIso_hom_inv :
    (projectiveIso C).hom ≫ (projectiveIso C⁻¹).hom = 𝟙 _ := by
  rw [projectiveIso_inv]
  exact (projectiveIso C).hom_inv_id

end FLT.Mazur.WeierstrassVariableChangeLinear
