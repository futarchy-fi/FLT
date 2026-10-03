/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SurjectiveDominantEpi
/-!
# Gluing local descents under a schematic epimorphism

Surjective schematic dominance gives the epimorphisms on open overlaps
needed to glue local descents, without assuming the normalization is flat.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
namespace FLT.Mazur.SchematicDescentGluing
variable {X Y Z : Scheme.{u}}
/-- Local descents on an open cover glue uniquely to the whole target. -/
theorem exists_desc_of_cover (π : X ⟶ Y) [Surjective π] [QuasiCompact π]
    [IsSchemeTheoreticallyDominant π] (h : X ⟶ Z) (𝒰 : Y.OpenCover)
    (u : ∀ i, 𝒰.X i ⟶ Z)
    (hfac : ∀ i, pullback.fst π (𝒰.f i) ≫ h = pullback.snd π (𝒰.f i) ≫ u i) :
    ∃! d : Y ⟶ Z, π ≫ d = h := by
  let : Epi π := SurjectiveDominantEpi.epi π
  suffices hd : ∃ d : Y ⟶ Z, π ≫ d = h by
    obtain ⟨d, hd⟩ := hd
    exact ⟨d, hd, fun e he ↦ (cancel_epi π).mp (he.trans hd.symm)⟩
  refine ⟨𝒰.glueMorphisms u ?_, ?_⟩
  · intro i j
    let : Epi (pullback.snd π (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i)) :=
      SurjectiveDominantEpi.epi _
    rw [← cancel_epi (pullback.snd π (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i)),
      ← cancel_epi (pullback.congrHom rfl pullback.condition.symm).hom]
    conv_rhs =>
      simp only [pullback.congrHom_hom, limit.lift_π_assoc, PullbackCone.mk_pt, cospan_right,
      PullbackCone.mk_π_app, Category.comp_id]
    rw [← pullbackLeftPullbackSndIso_inv_snd_snd, Category.assoc,
      ← pullbackLeftPullbackSndIso_inv_snd_snd, Category.assoc, ← pullback.condition_assoc,
      ← hfac i, ← pullback.condition_assoc, ← hfac j]
    simp
  · apply Scheme.Cover.hom_ext (𝒰.pullback₁ π)
    intro i
    simp [pullback.condition_assoc, hfac]
end FLT.Mazur.SchematicDescentGluing
