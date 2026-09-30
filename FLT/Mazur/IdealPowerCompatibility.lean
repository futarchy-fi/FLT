/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineIdealPowerExtension

/-!
# Common powers and affine difference annihilation

A finite family of affine extensions can be restricted to one common exponent.
Two coherent morphisms agreeing on the complement of an ideal agree on a
constructed ideal-power multiple. These are ingredients for finite-cover
extension; this file does not construct the global ideal-power subsheaf or glue
morphisms across overlaps.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite PrimeSpectrum
open Scheme.Modules

universe u

namespace FLT.Mazur.IdealPowerCompatibility

open AffineIdealPowerExtension AffineCoherentSubmoduleRestriction
open PrincipalSubmoduleCoordinates AffineCoherentSubmoduleExtension IdealPowerLifting FCurve

variable {R : CommRingCat.{u}}

/-- Higher powers include into lower powers through the actual coefficient submodules. -/
def powerTransition (M : (Spec R).Modules) (J : Ideal R) {a b : ℕ} (h : a ≤ b) :
    powerMultiple M J b ⟶ powerMultiple M J a :=
  (tilde.functor R).map (ModuleCat.ofHom
    (Submodule.inclusion (Submodule.smul_mono_left (Ideal.pow_le_pow_right h))))

/-- Power transitions preserve the canonical inclusion into the original sheaf. -/
lemma powerTransition_comp (M : (Spec R).Modules) (J : Ideal R) {a b : ℕ} (h : a ≤ b) :
    powerTransition M J h ≫ powerMultipleι M J a = powerMultipleι M J b := by
  change (tilde.functor R).map _ ≫ ((tilde.functor R).map _ ≫ M.fromTildeΓ) = _
  rw [← Category.assoc, ← Functor.map_comp]
  rfl

/-- An affine extension remains an extension after increasing its exponent. -/
lemma extension_of_le {M N : (Spec R).Modules} (J : Ideal R) {a b : ℕ} (h : a ≤ b)
    (g : M.restrict (idealComplement J).ι ⟶ N.restrict (idealComplement J).ι)
    (f : powerMultiple M J a ⟶ N)
    (hf : (restrictFunctor (idealComplement J).ι).map f =
      (restrictFunctor (idealComplement J).ι).map (powerMultipleι M J a) ≫ g) :
    (restrictFunctor (idealComplement J).ι).map (powerTransition M J h ≫ f) =
      (restrictFunctor (idealComplement J).ι).map (powerMultipleι M J b) ≫ g := by
  rw [Functor.map_comp, hf, ← Category.assoc, ← Functor.map_comp, powerTransition_comp]

/-- All members of a finite family of actual affine comparisons extend with one exponent. -/
theorem exists_common_extensions {ι : Type u} [Finite ι] (R : ι → CommRingCat.{u})
    [∀ i, IsNoetherianRing (R i)] (M N : ∀ i, (Spec (R i)).Modules)
    [∀ i, (M i).IsFinitePresentation] [∀ i, (N i).IsFinitePresentation]
    (J : ∀ i, Ideal (R i)) (hJ : ∀ i, (J i).FG)
    (g : ∀ i, (M i).restrict (idealComplement (J i)).ι ⟶
      (N i).restrict (idealComplement (J i)).ι) :
    ∃ n : ℕ, ∀ i, ∃ f : powerMultiple (M i) (J i) n ⟶ N i,
      (restrictFunctor (idealComplement (J i)).ι).map f =
        (restrictFunctor (idealComplement (J i)).ι).map (powerMultipleι (M i) (J i) n) ≫ g i := by
  classical
  let indexFintype : Fintype ι := Fintype.ofFinite ι
  choose n f hf using fun i ↦ exists_extension_of_fg (J i) (hJ i) (g i)
  refine ⟨Finset.univ.sup n, fun i ↦ ?_⟩
  let h : n i ≤ Finset.univ.sup n := Finset.le_sup (Finset.mem_univ i)
  exact ⟨powerTransition (M i) (J i) h ≫ f i, extension_of_le (J i) h (g i) (f i) (hf i)⟩

/-- A morphism zero on an open is zero on sections of every smaller open. -/
lemma app_eq_zero_of_restrict {M N : (Spec R).Modules} (f : M ⟶ N)
    (U V : (Spec R).Opens) (hV : V ≤ U) (h : (restrictFunctor U.ι).map f = 0) :
    f.app V = 0 := by
  have hh := congrArg (fun k ↦ k.app (U.ι ⁻¹ᵁ V)) h
  change f.app (U.ι ''ᵁ (U.ι ⁻¹ᵁ V)) = 0 at hh
  have he : U.ι ''ᵁ (U.ι ⁻¹ᵁ V) = V := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr hV]
  rwa [he] at hh

/-- Vanishing on a principal open clears a power on each global section. -/
lemma section_pow_mem_ker {M N : (Spec R).Modules} [N.IsQuasicoherent]
    (f : M ⟶ N) (r : R) (h : f.app (basicOpen r) = 0)
    (m : moduleSpecΓFunctor.obj M) :
    ∃ n : ℕ, r ^ n • m ∈ (moduleSpecΓFunctor.map f).hom.ker := by
  have hz : toSections N r ((moduleSpecΓFunctor.map f).hom m) = 0 := by
    have hn := congr($((modulesSpecToSheaf.map f).hom.naturality (basicOpen r).leTop.op) m)
    change f.app (basicOpen r) (toSections M r m) = _ at hn
    rw [h] at hn
    exact hn.symm
  obtain ⟨⟨_, n, rfl⟩, hn⟩ :=
    (IsLocalizedModule.eq_iff_exists (.powers r) (toSections N r)).mp
      (hz.trans (map_zero (toSections N r)).symm)
  refine ⟨n, ?_⟩
  change (moduleSpecΓFunctor.map f).hom (r ^ n • m) = 0
  simpa only [_root_.map_smul, Submonoid.smul_def, smul_zero] using hn

/-- A coherent affine morphism vanishing off a finitely generated ideal is killed by a power. -/
theorem exists_power_kills {M N : (Spec R).Modules}
    [M.IsFinitePresentation] [N.IsQuasicoherent] (J : Ideal R) (hJ : J.FG) (f : M ⟶ N)
    (h : (restrictFunctor (idealComplement J).ι).map f = 0) :
    ∃ n : ℕ, powerMultipleι M J n ≫ f = 0 := by
  obtain ⟨s, rfl⟩ := hJ
  let c := (moduleSpecΓFunctor.map f).hom
  have : Module.Finite R (moduleSpecΓFunctor.obj M) := affineCoherent_finite_sections M
  have hloc (r : R) (hr : r ∈ s) :
      (⊤ : Submodule R (moduleSpecΓFunctor.obj M)).localized (.powers r) ≤
        c.ker.localized (.powers r) := by
    apply (Submodule.localized'gi (Localization.Away r) (.powers r)
      (LocalizedModule.mkLinearMap (.powers r) (moduleSpecΓFunctor.obj M))).gc _ _ |>.mpr
    intro m _
    apply (numerator_mem_away_iff _ r m).mpr
    apply section_pow_mem_ker f r
    apply app_eq_zero_of_restrict f _ _ _ h
    have he : idealComplement (Ideal.span (s : Set R)) = complement s :=
      Opens.ext (complement_coe s).symm
    rw [he]
    exact le_iSup (fun r : s ↦ (basicOpen (r : R) : (Spec R).Opens)) ⟨r, hr⟩
  obtain ⟨n, hn⟩ := exists_pow_smul_le_of_localized_le ⊤ c.ker Module.Finite.fg_top s hloc
  refine ⟨n, ?_⟩
  have he : (tilde.functor R).map (moduleSpecΓFunctor.map f) ≫ N.fromTildeΓ =
      M.fromTildeΓ ≫ f := fromTildeΓNatTrans.naturality f
  change ((tilde.functor R).map (ModuleCat.ofHom
    (Ideal.span (s : Set R) ^ n • (⊤ : Submodule R (moduleSpecΓFunctor.obj M))).subtype) ≫
      M.fromTildeΓ) ≫ f = 0
  rw [Category.assoc, ← he, ← Category.assoc, ← Functor.map_comp]
  have hz : ModuleCat.ofHom (Ideal.span (s : Set R) ^ n •
      (⊤ : Submodule R (moduleSpecΓFunctor.obj M))).subtype ≫ moduleSpecΓFunctor.map f = 0 := by
    apply ModuleCat.hom_ext
    ext x
    exact hn x.property
  rw [hz, Functor.map_zero, zero_comp]

/-- Two actual affine morphisms agreeing off the ideal agree on a derived ideal-power source. -/
theorem exists_power_equalizes {M N : (Spec R).Modules}
    [M.IsFinitePresentation] [N.IsQuasicoherent] (J : Ideal R) (hJ : J.FG) (f g : M ⟶ N)
    (h : (restrictFunctor (idealComplement J).ι).map f =
      (restrictFunctor (idealComplement J).ι).map g) :
    ∃ n : ℕ, powerMultipleι M J n ≫ f = powerMultipleι M J n ≫ g := by
  have : (restrictFunctor (idealComplement J).ι).Additive :=
    Functor.additive_of_preserves_binary_products _
  obtain ⟨n, hn⟩ := exists_power_kills J hJ (f - g) (by rw [Functor.map_sub, h, sub_self])
  exact ⟨n, sub_eq_zero.mp (by simpa only [Preadditive.comp_sub] using hn)⟩

/-- A finite collection of affine differences is killed at one common exponent. -/
theorem exists_common_equalizers {ι : Type u} [Finite ι] (R : ι → CommRingCat.{u})
    (M N : ∀ i, (Spec (R i)).Modules)
    [∀ i, (M i).IsFinitePresentation] [∀ i, (N i).IsQuasicoherent]
    (J : ∀ i, Ideal (R i)) (hJ : ∀ i, (J i).FG) (f g : ∀ i, M i ⟶ N i)
    (h : ∀ i, (restrictFunctor (idealComplement (J i)).ι).map (f i) =
      (restrictFunctor (idealComplement (J i)).ι).map (g i)) :
    ∃ n : ℕ, ∀ i, powerMultipleι (M i) (J i) n ≫ f i =
      powerMultipleι (M i) (J i) n ≫ g i := by
  classical
  let indexFintype : Fintype ι := Fintype.ofFinite ι
  choose n hn using fun i ↦ exists_power_equalizes (J i) (hJ i) (f i) (g i) (h i)
  refine ⟨Finset.univ.sup n, fun i ↦ ?_⟩
  let hi : n i ≤ Finset.univ.sup n := Finset.le_sup (Finset.mem_univ i)
  rw [← powerTransition_comp (M i) (J i) hi, Category.assoc, hn i, Category.assoc]

end FLT.Mazur.IdealPowerCompatibility
