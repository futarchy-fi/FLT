/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeRelationGeneratorSubopens

/-!
# Naturality of effective generator descent

The compatible-function ring comparisons commute with the actual restriction
maps on every quotient subopen. Both forward restriction and inverse descent
therefore respect the original sheaf's restriction maps.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
universe u
namespace FLT.Mazur.RelativeRelationOrbit
open SchemeEffectiveEpiSections
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
/-- Original presheaf restrictions compose through any intermediate source open. -/
theorem generatorSource_restrict_trans {X : Scheme.{u}} {B C D : X.Opens}
    (hBC : B ≤ C) (hCD : C ≤ D) (v : Γ(X, D)) :
    X.presheaf.map (homOfLE hBC).op (X.presheaf.map (homOfLE hCD).op v) =
      X.presheaf.map (homOfLE (hBC.trans hCD)).op v := by
  change (X.presheaf.map (homOfLE hCD).op ≫ X.presheaf.map (homOfLE hBC).op) v = _
  rw [← Functor.map_comp]
  rfl

variable {S : Scheme.{u}} {A U : Over S} {p q : A ⟶ U}
  (e : CategoryTheory.EquivalenceRelation p q) (hq : IsOpenMap q.left)
  (W : U.left.Opens) {O₁ O₂ : TopologicalSpace.Opens (Orbit e)} (hO : O₁ ≤ O₂)

include hO in
/-- Original generator domains restrict along quotient-open inclusions. -/
theorem orbitGeneratorOpen_mono : orbitGeneratorOpen e W O₁ ≤ orbitGeneratorOpen e W O₂ :=
  fun _ hx ↦ ⟨hx.1, hO hx.2⟩

/-- The original invariant inclusion commutes with the unchanged source restriction maps. -/
theorem invariantInclusion_restrict
    (t : (invariantSheaf e).obj.obj (op O₂)) :
    (invariantInclusion e).hom.app (op O₁)
      ((invariantSheaf e).obj.map (homOfLE hO).op t) =
        U.left.presheaf.map (homOfLE (fun _ hx ↦ hO hx)).op
          ((invariantInclusion e).hom.app (op O₂) t) :=
  congrArg (fun k ↦ k t) ((invariantInclusion e).hom.naturality (homOfLE hO).op)

variable [Etale q.left] (h₁ : O₁ ≤ orbitImageOpen e hq W) (h₂ : O₂ ≤ orbitImageOpen e hq W)
local notation "C₁" => compatibleFunctions
  (SchemeRelationRestriction.fst p.left q.left (Scheme.Opens.ι (orbitGeneratorOpen e W O₁)))
  (SchemeRelationRestriction.snd p.left q.left (Scheme.Opens.ι (orbitGeneratorOpen e W O₁)))
local notation "C₂" => compatibleFunctions
  (SchemeRelationRestriction.fst p.left q.left (Scheme.Opens.ι (orbitGeneratorOpen e W O₂)))
  (SchemeRelationRestriction.snd p.left q.left (Scheme.Opens.ι (orbitGeneratorOpen e W O₂)))

/-- The comparison on every subopen commutes with the actual generator restriction. -/
theorem generatorSubopenFunctionEquiv_natural
    (t : (invariantSheaf e).obj.obj (op O₂)) :
    (Scheme.homOfLE _ (orbitGeneratorOpen_mono e W hO)).appTop
      (generatorSubopenFunctionEquiv e hq W O₂ h₂ t).val =
        (generatorSubopenFunctionEquiv e hq W O₁ h₁
          ((invariantSheaf e).obj.map (homOfLE hO).op t)).val := by
  rw [generatorSubopenFunctionEquiv_val, generatorSubopenFunctionEquiv_val,
    homOfLE_appTop_coordinates, invariantInclusion_restrict]
  apply congrArg (orbitGeneratorOpen e W O₁).topIso.inv
  exact (generatorSource_restrict_trans (X := U.left) (orbitGeneratorOpen_mono e W hO)
    (show orbitGeneratorOpen e W O₂ ≤ (pullOpen e O₂).val from inf_le_right) _).trans
      (generatorSource_restrict_trans
        (show orbitGeneratorOpen e W O₁ ≤ (pullOpen e O₁).val from inf_le_right)
        (show (pullOpen e O₁).val ≤ (pullOpen e O₂).val from fun _ hx ↦ hO hx) _).symm

include h₁ h₂ in
/-- Actual restriction preserves compatibility with all original restricted arrows. -/
theorem generatorFunctionRestriction_mem (v : C₂) :
    (Scheme.homOfLE _ (orbitGeneratorOpen_mono e W hO)).appTop v.val ∈ C₁ := by
  let t := (generatorSubopenFunctionEquiv e hq W O₂ h₂).symm v
  have ht : generatorSubopenFunctionEquiv e hq W O₂ h₂ t = v :=
    (generatorSubopenFunctionEquiv e hq W O₂ h₂).apply_symm_apply v
  rw [← ht, generatorSubopenFunctionEquiv_natural e hq W hO h₁ h₂]
  exact (generatorSubopenFunctionEquiv e hq W O₁ h₁ _).property

/-- The compatible-function restriction homomorphism is the original open immersion pullback. -/
def generatorFunctionRestriction : C₂ →+* C₁ := by
  let φ := (Scheme.homOfLE _ (orbitGeneratorOpen_mono e W hO)).appTop.hom
  exact (φ.comp (C₂).subtype).codRestrict _
    (generatorFunctionRestriction_mem e hq W hO h₁ h₂)

/-- Inverse effective descent is natural for the same original restriction maps. -/
theorem generatorSubopenFunctionEquiv_symm_natural (v : C₂) :
    (invariantSheaf e).obj.map (homOfLE hO).op
      ((generatorSubopenFunctionEquiv e hq W O₂ h₂).symm v) =
        (generatorSubopenFunctionEquiv e hq W O₁ h₁).symm
          (generatorFunctionRestriction e hq W hO h₁ h₂ v) := by
  apply (generatorSubopenFunctionEquiv e hq W O₁ h₁).injective
  rw [RingEquiv.apply_symm_apply]
  apply Subtype.ext
  rw [← generatorSubopenFunctionEquiv_natural e hq W hO h₁ h₂,
    RingEquiv.apply_symm_apply]
  rfl

end FLT.Mazur.RelativeRelationOrbit
