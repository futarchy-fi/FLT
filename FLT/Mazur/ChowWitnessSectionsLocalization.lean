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

/-!
# Local inputs for localization of Chow witness sections

The direct-image restriction map uses the actual structure-sheaf scalars.
On each affine chart, and each pairwise intersection, its coefficient direct
image over the affine base is localizing. These are the local inputs to the
finite equalizer argument; this file does not yet identify the equalizer with
the sections of the full Chow direct image.
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

This is the additive comparison. Transporting its scalar action and comparing it
with principal-open restriction are the remaining localization steps. -/
def graphPowerSectionsEqualizer (n : ℕ) (V : X.Opens) (hV : IsAffineOpen V) :
    Γ(graphPowerOver f n V, ⊤) ≃+
      CechSheafH.zeroCocycles ⟨(graphPowerOver f n V).presheaf,
        (graphPowerOver f n V).isSheaf⟩ (graphAffineChart f V hV) :=
  CechSheafH.sectionsEquiv ⟨(graphPowerOver f n V).presheaf,
    (graphPowerOver f n V).isSheaf⟩ _ (iSup_graphAffineChart f V hV)

end FLT.Mazur.Chow
