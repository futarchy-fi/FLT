/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# The canonical section spectrum is universal for affine targets
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur

variable (X T : Scheme) [IsAffine T]

/-- Every map into an affine scheme factors uniquely through the actual section spectrum. -/
theorem toSpecΓ_existsUnique_factor (q : X ⟶ T) :
    ∃! b : Spec Γ(X, ⊤) ⟶ T, X.toSpecΓ ≫ b = q := by
  refine ⟨Spec.map q.appTop ≫ T.isoSpec.inv, ?_, ?_⟩
  · dsimp only
    rw [← Category.assoc, ← Scheme.toSpecΓ_naturality]
    change (q ≫ T.isoSpec.hom) ≫ T.isoSpec.inv = q
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  · intro b hb
    apply ext_of_isAffine
    have he := congrArg Scheme.Hom.appTop hb
    rw [Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop] at he
    apply (cancel_mono (Scheme.ΓSpecIso Γ(X, ⊤)).hom).mp
    rw [he]
    have hf : X.toSpecΓ ≫ (Spec.map q.appTop ≫ T.isoSpec.inv) = q := by
      rw [← Category.assoc, ← Scheme.toSpecΓ_naturality]
      change (q ≫ T.isoSpec.hom) ≫ T.isoSpec.inv = q
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    simpa only [Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop] using
      (congrArg Scheme.Hom.appTop hf).symm

end FLT.Mazur
