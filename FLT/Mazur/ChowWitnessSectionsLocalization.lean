/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ChowSimultaneousLineBundle
public import FLT.Mazur.AffinePushforwardQuasicoherent
public import FLT.Mazur.CechSheafH
public import FLT.Mazur.CoherentFreeSheaf
public import FLT.Mazur.ModuleSheafTensorAffine
public import Mathlib.Algebra.Module.LocalizedModule.Submodule

/-!
# Local inputs for localization of Chow witness sections

The direct-image restriction map uses the actual structure-sheaf scalars.
On each affine chart and pairwise intersection, the coefficient direct image
over the affine base is localizing. Actual sections form a base-linear
equalizer, and localization follows from localization of its two products.
The remaining step identifies the affine-piece section coordinates with those
in this equalizer and transports back to the original target open.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Scheme.Modules FLT.Mazur.FCurve

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace FLT.Mazur.Chow

variable {k : Type} [Field k] {X : Scheme} (f : X ⟶ Spec (.of k)) [IsProper f]

/-- The actual direct image of the natural tensor power of the Chow line bundle. -/
def graphPowerPushforward (n : ℕ) : X.Modules :=
  (pushforward (graphClosureπ f)).obj (graphLineBundlePower f n)

/-- Principal-open sections with scalars restricted from the original target open. -/
abbrev graphPowerBasicSections (n : ℕ) (V : X.Opens) (r : Γ(X, V)) :
    ModuleCat Γ(X, V) :=
  (ModuleCat.restrictScalars
    (X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom).obj
      ((graphPowerPushforward f n).val.obj (op (X.basicOpen r)))

/-- The actual coefficient restriction, linear over the functions on the target open. -/
def graphPowerRestriction (n : ℕ) (V : X.Opens) (r : Γ(X, V)) :
    Γ(graphPowerPushforward f n, V) →ₗ[Γ(X, V)] graphPowerBasicSections f n V r :=
  { toFun := (graphPowerPushforward f n).presheaf.map
      (homOfLE (X.basicOpen_le r)).op
    map_add' := map_add _
    map_smul' := fun a s ↦ (graphPowerPushforward f n).val.map_smul _ a s }

/-- Local triviality gives a finite local presentation, without cohomological input. -/
theorem graphLineBundlePower_isFinitePresentation (n : ℕ) :
    (graphLineBundlePower f n).IsFinitePresentation := by
  apply coherent_of_neighborhoods
  intro x
  obtain ⟨U, hx, ⟨e⟩⟩ := graphLineBundlePower_locallyFreeRankOne f n x
  exact ⟨U, hx, (SheafOfModules.isFinitePresentation U.toScheme.ringCatSheaf).prop_of_iso
    e.symm (unitSheaf_isFinitePresentation U.toScheme)⟩

/-- The coefficient on the inverse image of a target open. -/
abbrev graphPowerOver (n : ℕ) (V : X.Opens) :
    (graphClosureπ f ⁻¹ᵁ V).toScheme.Modules :=
  (graphLineBundlePower f n).restrict (graphClosureπ f ⁻¹ᵁ V).ι

/-- Pushforward of one affine piece to the spectrum of the affine base. -/
def graphAffinePiecePushforward (n : ℕ) (V : X.Opens) (hV : IsAffineOpen V)
    (W : (graphClosureπ f ⁻¹ᵁ V).toScheme.Opens) : (Spec Γ(X, V)).Modules :=
  (pushforward (W.ι ≫ (graphClosureπ f ∣_ V) ≫ hV.isoSpec.hom)).obj
    ((graphPowerOver f n V).restrict W.ι)

/-- An affine piece has quasi-coherent direct image on the affine base. -/
theorem graphAffinePiecePushforward_isQuasicoherent (n : ℕ) (V : X.Opens)
    (hV : IsAffineOpen V) (W : (graphClosureπ f ⁻¹ᵁ V).toScheme.Opens)
    (hW : IsAffineOpen W) : (graphAffinePiecePushforward f n V hV W).IsQuasicoherent := by
  let : (graphLineBundlePower f n).IsFinitePresentation :=
    graphLineBundlePower_isFinitePresentation f n
  let : IsAffine W.toScheme := hW
  exact affineSchemePushforward_isQuasicoherent _ _

/-- Restriction for an affine piece is localization at the given base section. -/
theorem graphAffinePieceRestriction_isLocalized (n : ℕ) (V : X.Opens)
    (hV : IsAffineOpen V) (W : (graphClosureπ f ⁻¹ᵁ V).toScheme.Opens)
    (hW : IsAffineOpen W) (r : Γ(X, V)) :
    IsLocalizedModule (.powers r) (ModuleSheafTensor.affineRestriction
      (graphAffinePiecePushforward f n V hV W) r) := by
  let := graphAffinePiecePushforward_isQuasicoherent f n V hV W hW
  infer_instance

/-- In particular, every standard Chow chart has the required localization. -/
theorem graphAffineChartRestriction_isLocalized (n : ℕ) (V : X.Opens)
    (hV : IsAffineOpen V) (a : Fin (graphProjectiveDimension f + 1)) (r : Γ(X, V)) :
    IsLocalizedModule (.powers r) (ModuleSheafTensor.affineRestriction
      (graphAffinePiecePushforward f n V hV (graphAffineChart f V hV a)) r) :=
  graphAffinePieceRestriction_isLocalized f n V hV _ (graphAffineChart_isAffine f V hV a) r

/-- Pairwise intersections of the finite standard cover are affine. -/
theorem graphAffineChart_inf_isAffine (V : X.Opens) (hV : IsAffineOpen V)
    (a b : Fin (graphProjectiveDimension f + 1)) :
    IsAffineOpen (graphAffineChart f V hV a ⊓ graphAffineChart f V hV b) := by
  let : (graphClosure f).IsSeparated := ⟨by
    rw [← Limits.terminal.comp_from (graphClosureπ f ≫ f)]
    infer_instance⟩
  let : (graphClosureπ f ⁻¹ᵁ V).toScheme.IsSeparated := ⟨by
    rw [← Limits.terminal.comp_from (graphClosureπ f ⁻¹ᵁ V).ι]
    infer_instance⟩
  exact (graphAffineChart_isAffine f V hV a).inf (graphAffineChart_isAffine f V hV b)

/-- The overlap terms in the finite equalizer localize at the same base section. -/
theorem graphAffineOverlapRestriction_isLocalized (n : ℕ) (V : X.Opens)
    (hV : IsAffineOpen V) (a b : Fin (graphProjectiveDimension f + 1)) (r : Γ(X, V)) :
    IsLocalizedModule (.powers r) (ModuleSheafTensor.affineRestriction
      (graphAffinePiecePushforward f n V hV
        (graphAffineChart f V hV a ⊓ graphAffineChart f V hV b)) r) :=
  graphAffinePieceRestriction_isLocalized f n V hV _ (graphAffineChart_inf_isAffine f V hV a b) r

/-- The product restriction on all standard affine pieces uses one base-ring action. -/
def graphChartProductRestriction (n : ℕ) (V : X.Opens) (hV : IsAffineOpen V)
    (r : Γ(X, V)) :
    (∀ a, Γ(graphAffinePiecePushforward f n V hV (graphAffineChart f V hV a), ⊤)) →ₗ[Γ(X, V)]
      ∀ a, Γ(graphAffinePiecePushforward f n V hV (graphAffineChart f V hV a),
        PrimeSpectrum.basicOpen r) :=
  LinearMap.pi fun a ↦ (ModuleSheafTensor.affineRestriction
    (graphAffinePiecePushforward f n V hV (graphAffineChart f V hV a)) r).comp
      (LinearMap.proj a)

/-- Finiteness of the standard cover makes its product of restrictions localizing. -/
theorem graphChartProductRestriction_isLocalized (n : ℕ) (V : X.Opens)
    (hV : IsAffineOpen V) (r : Γ(X, V)) :
    IsLocalizedModule (.powers r) (graphChartProductRestriction f n V hV r) := by
  have (a : Fin (graphProjectiveDimension f + 1)) :=
    graphAffineChartRestriction_isLocalized f n V hV a r
  exact IsLocalizedModule.pi _ _

/-- The product of pairwise-overlap restriction maps. -/
def graphOverlapProductRestriction (n : ℕ) (V : X.Opens) (hV : IsAffineOpen V)
    (r : Γ(X, V)) :
    (∀ ab : Fin (graphProjectiveDimension f + 1) × Fin (graphProjectiveDimension f + 1),
      Γ(graphAffinePiecePushforward f n V hV
        (graphAffineChart f V hV ab.1 ⊓ graphAffineChart f V hV ab.2), ⊤)) →ₗ[Γ(X, V)]
    ∀ ab : Fin (graphProjectiveDimension f + 1) × Fin (graphProjectiveDimension f + 1),
      Γ(graphAffinePiecePushforward f n V hV
        (graphAffineChart f V hV ab.1 ⊓ graphAffineChart f V hV ab.2),
        PrimeSpectrum.basicOpen r) :=
  LinearMap.pi fun ab ↦ (ModuleSheafTensor.affineRestriction
    (graphAffinePiecePushforward f n V hV
      (graphAffineChart f V hV ab.1 ⊓ graphAffineChart f V hV ab.2)) r).comp
        (LinearMap.proj ab)

/-- The overlap product also localizes at the same base-ring element. -/
theorem graphOverlapProductRestriction_isLocalized (n : ℕ) (V : X.Opens)
    (hV : IsAffineOpen V) (r : Γ(X, V)) :
    IsLocalizedModule (.powers r) (graphOverlapProductRestriction f n V hV r) := by
  have (ab : Fin (graphProjectiveDimension f + 1) × Fin (graphProjectiveDimension f + 1)) :=
    graphAffineOverlapRestriction_isLocalized f n V hV ab.1 ab.2 r
  exact IsLocalizedModule.pi _ _

/-- The finite affine cover computes actual sections by its compatibility equalizer.

This additive comparison is refined below to a base-linear kernel comparison
compatible with restriction to every open. -/
def graphPowerSectionsEqualizer (n : ℕ) (V : X.Opens) (hV : IsAffineOpen V) :
    Γ(graphPowerOver f n V, ⊤) ≃+
      CechSheafH.zeroCocycles ⟨(graphPowerOver f n V).presheaf,
        (graphPowerOver f n V).isSheaf⟩ (graphAffineChart f V hV) :=
  CechSheafH.sectionsEquiv ⟨(graphPowerOver f n V).presheaf,
    (graphPowerOver f n V).isSheaf⟩ _ (iSup_graphAffineChart f V hV)

section Equalizer

variable {Y : Scheme} {R : Type} [CommRing R] (M : Y.Modules) (ρ : R →+* Γ(Y, ⊤))

/-- Sections on an open with scalars induced by a fixed base-ring map. -/
abbrev baseSections (W : Y.Opens) : ModuleCat R :=
  (ModuleCat.restrictScalars ((Y.presheaf.map W.leTop.op).hom.comp ρ)).obj (M.val.obj (op W))

/-- Actual restriction of sections is linear for the fixed base-ring action. -/
def baseRestriction {W T : Y.Opens} (h : W ≤ T) :
    baseSections M ρ T →ₗ[R] baseSections M ρ W where
  toFun := M.presheaf.map (homOfLE h).op
  map_add' := map_add _
  map_smul' r s := by
    change M.presheaf.map (homOfLE h).op ((Y.presheaf.map T.leTop.op) (ρ r) • s) =
      (Y.presheaf.map W.leTop.op) (ρ r) • M.presheaf.map (homOfLE h).op s
    rw [M.map_smul]
    congr 1
    exact congr($((Y.presheaf.map_comp T.leTop.op (homOfLE h).op).symm) (ρ r))

/-- Restrictions compose with the same scalar action on all three opens. -/
lemma baseRestriction_comp {A B C : Y.Opens} (h : A ≤ B) (g : B ≤ C) :
    (baseRestriction M ρ h).comp (baseRestriction M ρ g) =
      baseRestriction M ρ (h.trans g) := by
  ext s
  exact congr($((M.presheaf.map_comp (homOfLE g).op (homOfLE h).op).symm) s)

variable {ι : Type} (W : ι → Y.Opens)

/-- The overlap difference as a linear map over the specified base ring. -/
def baseDifference : (∀ i, baseSections M ρ (W i)) →ₗ[R]
    ∀ ij : ι × ι, baseSections M ρ (W ij.1 ⊓ W ij.2) :=
  LinearMap.pi fun ij ↦
    (baseRestriction M ρ inf_le_right).comp (LinearMap.proj ij.2) -
      (baseRestriction M ρ inf_le_left).comp (LinearMap.proj ij.1)

/-- The linear kernel is the actual compatibility condition on the cover. -/
lemma baseDifference_mem_ker (s : ∀ i, baseSections M ρ (W i)) :
    s ∈ (baseDifference M ρ W).ker ↔
      TopCat.Presheaf.IsCompatible M.presheaf W s := by
  simp only [LinearMap.mem_ker, baseDifference, LinearMap.pi_apply, LinearMap.sub_apply,
    LinearMap.comp_apply, LinearMap.proj_apply, funext_iff, Pi.zero_apply, sub_eq_zero,
    TopCat.Presheaf.IsCompatible]
  exact ⟨fun h i j ↦ (h (i, j)).symm, fun h ij ↦ (h ij.1 ij.2).symm⟩

/-- Restriction to the cover takes values in the linear compatibility kernel. -/
def baseRestrictEqualizer : baseSections M ρ ⊤ →ₗ[R] (baseDifference M ρ W).ker where
  toFun s := ⟨fun i ↦ baseRestriction M ρ le_top s, by
    rw [baseDifference_mem_ker]
    intro i j
    exact congr($((M.presheaf.map_comp (homOfLE le_top).op (homOfLE inf_le_left).op).symm) s)
      |>.trans (congr($((M.presheaf.map_comp
        (homOfLE le_top).op (homOfLE inf_le_right).op)) s))⟩
  map_add' s t := by ext i; exact (baseRestriction M ρ le_top).map_add s t
  map_smul' r s := by ext i; exact (baseRestriction M ρ le_top).map_smul r s

/-- Sheaf gluing proves bijectivity of the base-linear equalizer comparison. -/
theorem baseRestrictEqualizer_bijective (hW : ⨆ i, W i = ⊤) :
    Function.Bijective (baseRestrictEqualizer M ρ W) := by
  let F : TopCat.Sheaf AddCommGrpCat Y := ⟨M.presheaf, M.isSheaf⟩
  constructor
  · intro s t h
    apply F.eq_of_locally_eq' W ⊤ (fun _ ↦ homOfLE le_top) (ge_of_eq hW)
    intro i
    exact congrArg (fun z : (baseDifference M ρ W).ker ↦ z.val i) h
  · intro s
    obtain ⟨t, ht, -⟩ := F.existsUnique_gluing' W ⊤ (fun _ ↦ homOfLE le_top)
      (ge_of_eq hW) s.val ((baseDifference_mem_ker M ρ W s.val).mp s.property)
    exact ⟨t, Subtype.ext (funext ht)⟩

/-- Actual sections are the cover equalizer with their base-ring action retained. -/
def baseSectionsEqualizer (hW : ⨆ i, W i = ⊤) :
    baseSections M ρ ⊤ ≃ₗ[R] (baseDifference M ρ W).ker :=
  LinearEquiv.ofBijective (baseRestrictEqualizer M ρ W)
    (baseRestrictEqualizer_bijective M ρ W hW)

/-- The equalizer coordinates are the actual coefficient restriction maps. -/
@[simp]
lemma baseSectionsEqualizer_apply (hW : ⨆ i, W i = ⊤) (s : baseSections M ρ ⊤) (i : ι) :
    (baseSectionsEqualizer M ρ W hW s).val i = baseRestriction M ρ le_top s := rfl

/-- Restriction from an arbitrary open to the intersections with the fixed cover. -/
def baseOpenRestrictEqualizer (B : Y.Opens) :
    baseSections M ρ B →ₗ[R] (baseDifference M ρ (fun i ↦ W i ⊓ B)).ker where
  toFun s := ⟨fun i ↦ baseRestriction M ρ inf_le_right s, by
    rw [baseDifference_mem_ker]
    intro i j
    exact congr($((M.presheaf.map_comp (homOfLE inf_le_right).op
      (homOfLE inf_le_left).op).symm) s) |>.trans
        (congr($((M.presheaf.map_comp (homOfLE inf_le_right).op
          (homOfLE inf_le_right).op)) s))⟩
  map_add' s t := by ext i; exact (baseRestriction M ρ inf_le_right).map_add s t
  map_smul' r s := by ext i; exact (baseRestriction M ρ inf_le_right).map_smul r s

/-- The same equalizer computes sections on every open, with the original base scalars. -/
theorem baseOpenRestrictEqualizer_bijective (hW : ⨆ i, W i = ⊤) (B : Y.Opens) :
    Function.Bijective (baseOpenRestrictEqualizer M ρ W B) := by
  let F : TopCat.Sheaf AddCommGrpCat Y := ⟨M.presheaf, M.isSheaf⟩
  have hB : B ≤ ⨆ i, W i ⊓ B := by rw [← iSup_inf_eq, hW, top_inf_eq]
  constructor
  · intro s t h
    apply F.eq_of_locally_eq' (fun i ↦ W i ⊓ B) B (fun _ ↦ homOfLE inf_le_right) hB
    intro i
    exact congrArg (fun z : (baseDifference M ρ (fun i ↦ W i ⊓ B)).ker ↦ z.val i) h
  · intro s
    obtain ⟨t, ht, -⟩ := F.existsUnique_gluing' (fun i ↦ W i ⊓ B) B
      (fun _ ↦ homOfLE inf_le_right) hB s.val
        ((baseDifference_mem_ker M ρ _ s.val).mp s.property)
    exact ⟨t, Subtype.ext (funext ht)⟩

/-- The base-linear comparison on every open, in particular an inverse-image principal open. -/
def baseOpenSectionsEqualizer (hW : ⨆ i, W i = ⊤) (B : Y.Opens) :
    baseSections M ρ B ≃ₗ[R] (baseDifference M ρ (fun i ↦ W i ⊓ B)).ker :=
  LinearEquiv.ofBijective (baseOpenRestrictEqualizer M ρ W B)
    (baseOpenRestrictEqualizer_bijective M ρ W hW B)

/-- Componentwise restriction of the chart product to its intersections with an open. -/
def baseProductRestriction (B : Y.Opens) :
    (∀ i, baseSections M ρ (W i)) →ₗ[R] ∀ i, baseSections M ρ (W i ⊓ B) :=
  LinearMap.pi fun i ↦ (baseRestriction M ρ inf_le_left).comp (LinearMap.proj i)

/-- Componentwise restriction on the overlap product. -/
def baseOverlapRestriction (B : Y.Opens) :
    (∀ ij : ι × ι, baseSections M ρ (W ij.1 ⊓ W ij.2)) →ₗ[R]
      ∀ ij : ι × ι, baseSections M ρ ((W ij.1 ⊓ B) ⊓ (W ij.2 ⊓ B)) :=
  LinearMap.pi fun ij ↦
    (baseRestriction M ρ (inf_le_inf inf_le_left inf_le_left)).comp (LinearMap.proj ij)

/-- The actual restrictions commute with the overlap difference, over the base ring. -/
lemma baseDifference_restriction (B : Y.Opens) :
    (baseDifference M ρ (fun i ↦ W i ⊓ B)).comp (baseProductRestriction M ρ W B) =
      (baseOverlapRestriction M ρ W B).comp (baseDifference M ρ W) := by
  ext s ij
  change M.presheaf.map (homOfLE inf_le_right).op
      (M.presheaf.map (homOfLE inf_le_left).op (s ij.2)) -
    M.presheaf.map (homOfLE inf_le_left).op
      (M.presheaf.map (homOfLE inf_le_left).op (s ij.1)) =
    M.presheaf.map (homOfLE (inf_le_inf inf_le_left inf_le_left)).op
      (M.presheaf.map (homOfLE inf_le_right).op (s ij.2) -
        M.presheaf.map (homOfLE inf_le_left).op (s ij.1))
  rw [map_sub]
  simp only [← M.presheaf.map_comp_apply, ← op_comp, homOfLE_comp]

/-- Restriction of sections agrees with componentwise restriction in equalizer coordinates. -/
lemma baseSectionsEqualizer_restriction (hW : ⨆ i, W i = ⊤) (B : Y.Opens)
    (s : baseSections M ρ ⊤) :
    (baseOpenSectionsEqualizer M ρ W hW B (baseRestriction M ρ le_top s)).val =
      baseProductRestriction M ρ W B (baseSectionsEqualizer M ρ W hW s).val := by
  funext i
  exact congr($((M.presheaf.map_comp (homOfLE le_top).op
    (homOfLE inf_le_right).op).symm) s) |>.trans
      (congr($((M.presheaf.map_comp (homOfLE le_top).op (homOfLE inf_le_left).op)) s))

/-- Exactness of localization transfers the two product localizations to actual sections.

The hypotheses concern the cover and overlap restriction maps, not the desired
section restriction. The equalizer and both commuting squares were proved above. -/
theorem baseRestriction_isLocalized_of_products (hW : ⨆ i, W i = ⊤) (B : Y.Opens)
    (r : R) [IsLocalizedModule (.powers r) (baseProductRestriction M ρ W B)]
    [IsLocalizedModule (.powers r) (baseOverlapRestriction M ρ W B)] :
    IsLocalizedModule (.powers r) (baseRestriction M ρ (show B ≤ ⊤ from le_top)) := by
  let p := baseProductRestriction M ρ W B
  let q := baseOverlapRestriction M ρ W B
  let d := baseDifference M ρ W
  let dB := baseDifference M ρ (fun i ↦ W i ⊓ B)
  have hd : IsLocalizedModule.map (.powers r) p q d = dB := by
    apply IsLocalizedModule.linearMap_ext (.powers r) p q
    ext s ij
    change IsLocalizedModule.map (.powers r) p q d (p s) ij = dB (p s) ij
    rw [IsLocalizedModule.map_apply]
    exact congrArg (fun t ↦ t s ij) (baseDifference_restriction M ρ W B).symm
  let := IsLocalizedModule.module (A := Localization (.powers r)) (.powers r) p
  let := IsLocalizedModule.module (A := Localization (.powers r)) (.powers r) q
  let := IsLocalizedModule.isScalarTower_module (A := Localization (.powers r)) (.powers r) p
  let := IsLocalizedModule.isScalarTower_module (A := Localization (.powers r)) (.powers r) q
  let t := LinearMap.toKerIsLocalized (.powers r) p q d
  let ht := LinearMap.toKerLocalized_isLocalizedModule (Localization (.powers r))
    (.powers r) p q d
  let e : (IsLocalizedModule.map (.powers r) p q d).ker ≃ₗ[R] dB.ker :=
    LinearEquiv.ofEq _ _ (congrArg LinearMap.ker hd)
  let h := IsLocalizedModule.of_linearEquiv (.powers r) t e
  let a := baseSectionsEqualizer M ρ W hW
  let b := baseOpenSectionsEqualizer M ρ W hW B
  have hcomp := IsLocalizedModule.of_linearEquiv_right (.powers r) (e.toLinearMap.comp t) a
  apply (IsLocalizedModule.comp_iff_of_bijective_left (.powers r) b.toLinearMap b.bijective).mp
  convert hcomp using 1
  ext s i
  exact congrFun (baseSectionsEqualizer_restriction M ρ W hW B s) i

end Equalizer

/-- The actual affine-target structure map gives the scalar action on Chow sections. -/
def graphPowerBaseScalars (V : X.Opens) (hV : IsAffineOpen V) :
    Γ(X, V) →+* Γ((graphClosureπ f ⁻¹ᵁ V).toScheme, ⊤) :=
  ((Scheme.ΓSpecIso Γ(X, V)).inv ≫ ((graphClosureπ f ∣_ V) ≫ hV.isoSpec.hom).appTop).hom

/-- The standard Chow cover computes sections as a linear equalizer over the affine base. -/
def graphPowerBaseSectionsEqualizer (n : ℕ) (V : X.Opens) (hV : IsAffineOpen V) :
    baseSections (graphPowerOver f n V) (graphPowerBaseScalars f V hV) ⊤ ≃ₗ[Γ(X, V)]
      (baseDifference (graphPowerOver f n V) (graphPowerBaseScalars f V hV)
        (graphAffineChart f V hV)).ker :=
  baseSectionsEqualizer _ _ _ (iSup_graphAffineChart f V hV)

end FLT.Mazur.Chow
