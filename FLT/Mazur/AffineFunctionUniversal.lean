/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffinizationUniversal

/-!
# Affine targets with unchanged global functions are actual affinizations
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.AffineFunctionUniversal

variable {X Y : Scheme} (f : X ⟶ Y) [IsAffine Y] [IsIso f.appTop]

/-- The target is canonically the spectrum of the original source functions. -/
def spectrumIso : Spec Γ(X, ⊤) ≅ Y :=
  asIso (Spec.map f.appTop) ≪≫ Y.isoSpec.symm

/-- The original morphism is exactly the canonical affinization under this identification. -/
@[reassoc] theorem spectrumIso_fac : X.toSpecΓ ≫ (spectrumIso f).hom = f := by
  change X.toSpecΓ ≫ Spec.map f.appTop ≫ Y.isoSpec.inv = f
  rw [← Scheme.toSpecΓ_naturality_assoc]
  change f ≫ Y.isoSpec.hom ≫ Y.isoSpec.inv = f
  simp only [Iso.hom_inv_id, Category.comp_id]

/-- Every affine-valued morphism factors uniquely through the original map. -/
theorem existsUnique_factor (T : Scheme) [IsAffine T] (q : X ⟶ T) :
    ∃! b : Y ⟶ T, f ≫ b = q := by
  let e := spectrumIso f
  obtain ⟨b, hb, hu⟩ := toSpecΓ_existsUnique_factor X T q
  refine ⟨e.inv ≫ b, ?_, ?_⟩
  · dsimp only
    rw [← spectrumIso_fac f, Category.assoc, Iso.hom_inv_id_assoc]
    exact hb
  · intro d hd
    have he : e.hom ≫ d = b := hu _ (by
      dsimp only
      rw [← Category.assoc, spectrumIso_fac]
      exact hd)
    rw [← he, Iso.inv_hom_id_assoc]

/-- Pullback along the original affinization detects affine-valued morphisms. -/
theorem affine_hom_ext (T : Scheme) [IsAffine T] (a b : Y ⟶ T)
    (h : f ≫ a = f ≫ b) : a = b := by
  obtain ⟨c, _, hc⟩ := existsUnique_factor f T (f ≫ b)
  exact (hc a h).trans (hc b rfl).symm

end FLT.Mazur.AffineFunctionUniversal
