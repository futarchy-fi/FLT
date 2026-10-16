/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffinePicardSections

/-!
# Affine reconstruction retains the specified section coordinates

The affine reconstruction isomorphism acts on global sections by precisely
the supplied linear equivalence. This permits equation frames with a fixed
generator instead of an unrelated chosen Cartier-chart generator.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.SchemePicard
open AffineModuleGlobalSections
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X : Scheme.{u}} [IsAffine X] {M N : X.Modules}
variable [M.IsQuasicoherent] [N.IsQuasicoherent]

/-- Affine reconstruction induces the original linear equivalence on global sections. -/
theorem isoOfSections_sections (e : Γ(M, ⊤) ≃ₗ[Γ(X, ⊤)] Γ(N, ⊤)) :
    (sections X).map (isoOfSections e).hom = e.toModuleIso.hom := by
  simp only [isoOfSections, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    asIso_hom, asIso_inv, Functor.map_comp, Functor.map_inv]
  have ht := (affineAdjunction X).right_triangle_components M
  have hu : (affineAdjunction X).unit.app ((sections X).obj M) =
      inv ((sections X).map ((affineAdjunction X).counit.app M)) := by
    apply (cancel_mono ((sections X).map ((affineAdjunction X).counit.app M))).mp
    rw [ht, IsIso.inv_hom_id]
    rfl
  rw [← hu]
  change (affineAdjunction X).unit.app ((sections X).obj M) ≫
    ((affineTilde X ⋙ sections X).map e.toModuleIso.hom) ≫
      (sections X).map ((affineAdjunction X).counit.app N) = _
  rw [← Category.assoc, ← (affineAdjunction X).unit.naturality, Category.assoc]
  change e.toModuleIso.hom ≫ (affineAdjunction X).unit.app ((sections X).obj N) ≫
    (sections X).map ((affineAdjunction X).counit.app N) = _
  rw [(affineAdjunction X).right_triangle_components]
  rfl

/-- Evaluation of the reconstructed frame is exactly evaluation in its specified coordinates. -/
theorem isoOfSections_apply (e : Γ(M, ⊤) ≃ₗ[Γ(X, ⊤)] Γ(N, ⊤)) (s : Γ(M, ⊤)) :
    (isoOfSections e).hom.app ⊤ s = e s :=
  congrArg (fun f ↦ f s) (isoOfSections_sections e)

end FLT.Mazur.SchemePicard
