/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonNormalizationChart
public import FLT.Mazur.ModuleExactOpenCover
/-!
# Global exactness for the one-gon normalization

On the torus chart the normalization is an isomorphism and the node image is zero.
Together with the pinched affine chart, this proves the actual sheaf sequence exact.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
@[expose] public noncomputable section
universe u
namespace FLT.Mazur.OneGonNormalizationTorus
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open OneGonNormalizationChart OneGonNormalization PolygonNodePresentation
open Scheme.Modules StructureDirectImage
variable (K : Type u) [Field K]

theorem nodes_preimage_torus :
    (nodes K).left ⁻¹ᵁ (OneGonGluing.torus K).opensRange = ⊥ := by
  ext z
  change (nodes K).left z ∈ Set.range (OneGonGluing.torus K) ↔ False
  apply iff_false_intro
  rintro ⟨y, hy⟩
  obtain ⟨x, rfl⟩ := (PolygonPinching.nodeι K 1 0).left.homeomorph.surjective z
  have he : OneGonGluing.node K (bOrigin K x) = OneGonGluing.torus K y := by
    exact (congrArg (fun f ↦ f x) (nodeι_nodes K 0)).symm.trans hy.symm
  obtain ⟨t, ht, _⟩ := OneGonNormalizationPullback.intersection K _ _ he
  have hp : bOrigin K x ∈ Set.range (bPuncture K) := ⟨t, ht⟩
  rw [range_bPuncture] at hp
  change bEval (u (R := K)) ∉ x.asIdeal at hp
  apply hp
  have hu : bEval (u (R := K)) = 0 := by simp [bEval, u]
  rw [hu]
  exact Ideal.zero_mem _

theorem image_restrict_isZero {X Y U : Scheme.{u}} (f : X ⟶ Y) (j : U ⟶ Y)
    [IsOpenImmersion j] (h : f ⁻¹ᵁ j.opensRange = ⊥) :
    IsZero ((image f).restrict j) := by
  rw [IsZero.iff_id_eq_zero]
  ext W r
  have he : f ⁻¹ᵁ (j ''ᵁ W) = ⊥ := by
    apply le_bot_iff.mp
    exact (f.preimage_mono (j.image_le_opensRange W)).trans_eq h
  let : Subsingleton Γ(X, f ⁻¹ᵁ (j ''ᵁ W)) :=
    CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty he)
  exact @Subsingleton.elim Γ(X, f ⁻¹ᵁ (j ''ᵁ W)) inferInstance _ _

theorem torus_isPullback :
    IsPullback (𝟙 (OneGonGluing.torusChart K))
      (OneGonNormalizationPullback.torusLift K ≫ (PolygonPinching.componentι K 1 0).left)
      (OneGonGluing.torus K) (normalizationOver K).left := by
  apply (OneGonNormalizationPullback.torus_isPullback K).of_iso (Iso.refl _) (Iso.refl _)
    (asIso (PolygonPinching.componentι K 1 0).left) (Iso.refl _)
  · simp
  · simp
  · simp
  · dsimp only [Iso.refl_hom, asIso_hom]
    rw [Category.comp_id]
    exact (congrArg Over.Hom.left (componentι_normalizationOver K 0)).symm

theorem unitMap_id_iso (X : Scheme.{u}) : IsIso (unitMap (𝟙 X)) := by
  apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
  intro U
  change IsIso (𝟙 _)
  infer_instance

theorem torus_shortExact :
    ((complex K).map (restrictFunctor (OneGonGluing.torus K))).ShortExact := by
  let S := (complex K).map (restrictFunctor (OneGonGluing.torus K))
  have hzero : IsZero S.X₃ := image_restrict_isZero (nodes K).left
    (OneGonGluing.torus K) (nodes_preimage_torus K)
  let e := StructureImageOpenChart.iso (normalizationOver K).left (𝟙 _)
    (OneGonNormalizationPullback.torusLift K ≫ (PolygonPinching.componentι K 1 0).left)
    (OneGonGluing.torus K) (torus_isPullback K)
  have he : S.f ≫ e.hom = (restrictUnitIso (OneGonGluing.torus K)).hom ≫ unitMap (𝟙 _) :=
    StructureImageOpenChart.unit_iso _ _ _ _ _
  have : IsIso (unitMap (𝟙 (OneGonGluing.torusChart K))) := unitMap_id_iso _
  have : IsIso (S.f ≫ e.hom) := by rw [he]; infer_instance
  have hf : IsIso S.f := IsIso.of_isIso_comp_right _ e.hom
  exact (ShortComplex.Splitting.ofIsIsoOfIsZero S hf hzero).shortExact
theorem shortExact : (complex K).ShortExact := by
  apply ModuleExactOpenCover.shortExact_of_schemeCover _
    (OneGonNormalizationFinite.targetCover K)
  intro b
  cases b
  · exact node_shortExact K
  · exact torus_shortExact K
end FLT.Mazur.OneGonNormalizationTorus
