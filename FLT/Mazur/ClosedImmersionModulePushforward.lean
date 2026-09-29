/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IntegralClosedSupport

/-!
# Stalks and support of closed immersion module pushforward

Pushforward along a closed immersion preserves additive stalks on its image and
has zero stalks off the image. Consequently its support is the image of the
original support. The defining ideal kills the pushed-forward sheaf on affine
opens. Over Noetherian affine spectra, surjective ring maps preserve coherence.
Global coherence and descent of ideal-annihilated sheaves are not proved here.
All statements concern the actual scheme module pushforward.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.Modules

universe u

namespace FLT.Mazur.FCurve.CoherentDevissage

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]

/-- At a point of the closed subscheme, pushforward does not change the additive stalk. -/
def closedPushforwardStalkIso (M : X.Modules) (x : X) :
    (stalk (f x)).obj ((pushforward f).obj M) ≅ (stalk x).obj M := by
  have := TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing
    AddCommGrpCat f.isClosedEmbedding.isEmbedding.isInducing M.presheaf x
  exact asIso (M.presheaf.stalkPushforward AddCommGrpCat f.base x)

/-- Support at points of the image is detected on the original sheaf. -/
lemma mem_support_closedPushforward (M : X.Modules) (x : X) :
    f x ∈ support ((pushforward f).obj M) ↔ x ∈ support M :=
  not_congr (closedPushforwardStalkIso f M x).isZero_iff

/-- Outside the closed image there is a neighborhood with empty inverse image. -/
theorem closedPushforward_stalk_isZero (M : X.Modules) (y : Y)
    (hy : y ∉ Set.range f) : IsZero ((stalk y).obj ((pushforward f).obj M)) := by
  let U : Y.Opens := ⟨(Set.range f)ᶜ, f.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  have hU : f ⁻¹ᵁ U = ⊥ := by
    ext x
    simp [U]
  let N := (pushforward f).obj M
  apply (IsZero.iff_id_eq_zero _).mpr
  apply N.presheaf.stalk_hom_ext
  intro V hyV
  let W := U ⊓ V
  have hyW : y ∈ W := ⟨hy, hyV⟩
  have hg : N.presheaf.germ W y hyW = 0 := by
    rw [← Category.id_comp (N.presheaf.germ W y hyW)]
    have hzero : IsZero (N.presheaf.obj (op W)) := by
      apply (IsZero.iff_id_eq_zero _).mpr
      apply ((moduleToSheaf X).obj M |>.isTerminalOfEqEmpty ?_).hom_ext
      apply le_antisymm
      · exact hU ▸ (Opens.map f.base).monotone inf_le_left
      · exact bot_le
    rw [hzero.eq_of_src (𝟙 _) 0, zero_comp]
  change N.presheaf.germ V y hyV ≫ 𝟙 _ = N.presheaf.germ V y hyV ≫ 0
  simp only [Category.comp_id, comp_zero]
  rw [← N.presheaf.germ_res (homOfLE (show W ≤ V from inf_le_right)) y hyW, hg,
    comp_zero]

/-- The support of pushforward is exactly the image of the original support. -/
theorem support_closedPushforward (M : X.Modules) :
    support ((pushforward f).obj M) = f '' support M := by
  ext y
  constructor
  · intro hy
    have hyr : y ∈ Set.range f := by
      by_contra h
      exact hy (closedPushforward_stalk_isZero f M y h)
    obtain ⟨x, rfl⟩ := hyr
    exact ⟨x, (mem_support_closedPushforward f M x).mp hy, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact (mem_support_closedPushforward f M x).mpr hx

/-- In particular, support is contained in the closed image. -/
lemma support_closedPushforward_subset_range (M : X.Modules) :
    support ((pushforward f).obj M) ⊆ Set.range f := by
  rw [support_closedPushforward]
  exact Set.image_subset_range _ _

/-- Pushforward of a coherent sheaf has closed support, independently of coherence preservation. -/
theorem isClosed_support_closedPushforward (M : X.Modules) [M.IsFinitePresentation] :
    IsClosed (support ((pushforward f).obj M)) := by
  rw [support_closedPushforward]
  exact f.isClosedEmbedding.isClosedMap _ (isClosed_support M)

/-- Pushforward along a closed immersion detects vanishing of the sheaf. -/
theorem closedPushforward_isZero_iff (M : X.Modules) :
    IsZero ((pushforward f).obj M) ↔ IsZero M := by
  rw [← support_eq_empty_iff_isZero, ← support_eq_empty_iff_isZero,
    support_closedPushforward, Set.image_eq_empty]

omit [IsClosedImmersion f] in
/-- Sections of the defining ideal act by zero on every pushed-forward module sheaf. -/
theorem closedPushforward_ker_smul (M : X.Modules) (U : Y.affineOpens)
    (r : Γ(Y, U.1)) (hr : r ∈ f.ker.ideal U)
    (m : Γ((pushforward f).obj M, U.1)) : r • m = 0 := by
  change (M.smul ((f.app U.1).hom r)).hom m = 0
  simp only [RingHom.mem_ker.mp (f.ideal_ker_le U hr), map_zero, AddCommGrpCat.zero_apply]

/-- For an ideal-sheaf subscheme, the annihilating ideal is the prescribed ideal itself. -/
theorem subschemePushforward_ideal_smul (I : Y.IdealSheafData) (M : I.subscheme.Modules)
    (U : Y.affineOpens) (r : Γ(Y, U.1)) (hr : r ∈ I.ideal U)
    (m : Γ((pushforward I.subschemeι).obj M, U.1)) : r • m = 0 := by
  apply closedPushforward_ker_smul I.subschemeι M U r
  simpa only [I.ker_subschemeι] using hr

/-- The support of a sheaf pushed from a specified ideal-sheaf subscheme lies in its support. -/
lemma support_subschemePushforward_subset (I : Y.IdealSheafData) (M : I.subscheme.Modules) :
    support ((pushforward I.subschemeι).obj M) ⊆ I.support := by
  simpa only [I.range_subschemeι] using support_closedPushforward_subset_range I.subschemeι M

section Affine

variable {R S : CommRingCat.{u}} (φ : R ⟶ S)

/-- On affine schemes, global sections of pushforward are restriction of scalars. -/
def affinePushforwardSectionsIso (M : (Spec S).Modules) :
    moduleSpecΓFunctor.obj ((pushforward (Spec.map φ)).obj M) ≅
      (ModuleCat.restrictScalars φ.hom).obj (moduleSpecΓFunctor.obj M) :=
  (TopCat.Sheaf.forget (ModuleCat R) (Spec R) ⋙
    (evaluation _ _).obj (op ⊤)).mapIso ((pushforwardCompModulesSpecToSheafIso φ).app M)

/-- A coherent sheaf pushed along an affine closed immersion has finite global sections. -/
lemma affineClosedPushforward_finite_sections (hφ : Function.Surjective φ.hom)
    (M : (Spec S).Modules) [M.IsFinitePresentation] :
    Module.Finite R (moduleSpecΓFunctor.obj ((pushforward (Spec.map φ)).obj M)) := by
  let := φ.hom.toAlgebra
  have : Module.Finite R S := RingHom.Finite.of_surjective φ.hom hφ
  let N := moduleSpecΓFunctor.obj M
  have : Module.Finite S N := affineCoherent_finite_sections M
  let N' := (ModuleCat.restrictScalars φ.hom).obj N
  have : Module.Finite S N' := inferInstanceAs (Module.Finite S N)
  have : IsScalarTower R S N' := ⟨fun r s n ↦ mul_smul (φ r) s n⟩
  have : Module.Finite R N' := Module.Finite.trans S N'
  exact Module.Finite.equiv (affinePushforwardSectionsIso φ M).toLinearEquiv.symm

/-- Coherence of the actual pushforward along a surjection of Noetherian affine rings. -/
theorem affineClosedPushforward_isFinitePresentation [IsNoetherianRing R]
    (hφ : Function.Surjective φ.hom) (M : (Spec S).Modules) [M.IsFinitePresentation] :
    ((pushforward (Spec.map φ)).obj M).IsFinitePresentation := by
  have : Module.Finite R
      ((modulesSpecToSheaf.obj ((pushforward (Spec.map φ)).obj M)).presheaf.obj (op ⊤)) :=
    affineClosedPushforward_finite_sections φ hφ M
  have := isIso_fromTildeΓ_pushforward φ M
  exact (SheafOfModules.isFinitePresentation (Spec R).ringCatSheaf).prop_of_iso
    (asIso ((pushforward (Spec.map φ)).obj M).fromTildeΓ)
    (affineTilde_isFinitePresentation_of_finite _)

end Affine

end FLT.Mazur.FCurve.CoherentDevissage
