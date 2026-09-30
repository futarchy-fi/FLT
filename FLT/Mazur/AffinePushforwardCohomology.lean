/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.AffineCoverCohomology
public import FLT.Mazur.AffinePushforwardQuasicoherent
public import FLT.Mazur.ModuleCohomologyRing
public import FLT.Mazur.PushforwardCech

/-!
# Cohomology of affine direct images

For an affine morphism to a separated scheme, direct image preserves the
cohomology of a quasi-coherent module. The comparison is natural in the module
and linear over target global sections and any specified base ring.

This is the affine case of Stacks 01F4(1). Stacks 02O5 also uses 01F6 for a
non-affine Chow modification; that general acyclic-direct-image case is separate.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme.Modules

universe u v

namespace FLT.Mazur.FCurve

open CechSheafHZero

variable {X Y : Scheme.{u}} [Y.IsSeparated]
  (f : X ⟶ Y) [IsAffineHom f] (M : X.Modules) [M.IsQuasicoherent]

local instance affineCohomologyPushforwardQuasicoherent :
    ((pushforward f).obj M).IsQuasicoherent :=
  affinePushforward_isQuasicoherent f M

/-- The two affine-cover computations are identified by the actual direct-image sections. -/
def affinePushforwardCoverHEquiv {ι : Type u} (U : ι → Y.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (hCover : iSup U = ⊤) (n : ℕ) :
    letI _sourceScalars := Module.compHom (ModuleH M n) f.appTop.hom
    ModuleH ((pushforward f).obj M) n ≃ₗ[Γ(Y, ⊤)] ModuleH M n := by
  letI _sourceSeparated : X.IsSeparated := ⟨by
    rw [← terminal.comp_from f]
    infer_instance⟩
  letI _sourceCechScalars := Module.compHom
    (CH (fun i ↦ f ⁻¹ᵁ U i) (moduleAbelianSheaf M) n) f.appTop.hom
  letI _sourceScalars := Module.compHom (ModuleH M n) f.appTop.hom
  exact (affineCoverCechEquiv ((pushforward f).obj M) U hU hCover n).symm.trans
    ((PushforwardCech.moduleCechEquiv f U M n).trans
      (affineCoverRingCechEquiv M (fun i ↦ f ⁻¹ᵁ U i)
        (fun i ↦ (hU i).preimage f) (f.iSup_preimage_eq_top hCover) f.appTop.hom n))

/-- Affine direct image preserves cohomology, linearly over target global sections. -/
def affinePushforwardModuleHEquiv (n : ℕ) :
    letI _sourceScalars := Module.compHom (ModuleH M n) f.appTop.hom
    ModuleH ((pushforward f).obj M) n ≃ₗ[Γ(Y, ⊤)] ModuleH M n :=
  affinePushforwardCoverHEquiv f M (fun U : Y.affineOpens ↦ U.1)
    (fun U ↦ U.2) (iSup_affineOpens_eq_top Y) n

/-- Restriction of scalars gives affine-direct-image comparison over any base ring. -/
def affinePushforwardRingHEquiv {R : Type v} [Ring R]
    (ρ : R →+* Γ(Y, ⊤)) (n : ℕ) :
    letI _targetScalars := Module.compHom (ModuleH ((pushforward f).obj M) n) ρ
    letI _sourceScalars := Module.compHom (ModuleH M n) (f.appTop.hom.comp ρ)
    ModuleH ((pushforward f).obj M) n ≃ₗ[R] ModuleH M n := by
  letI _sourceTargetScalars := Module.compHom (ModuleH M n) f.appTop.hom
  letI _targetScalars := Module.compHom (ModuleH ((pushforward f).obj M) n) ρ
  letI _sourceScalars := Module.compHom (ModuleH M n) (f.appTop.hom.comp ρ)
  exact
    { toAddEquiv := (affinePushforwardModuleHEquiv f M n).toAddEquiv
      map_smul' := fun r x ↦ (affinePushforwardModuleHEquiv f M n).map_smul (ρ r) x }

/-- The comparison retains the specified structure morphisms over a field. -/
def affinePushforwardScalarHEquiv {k : Type u} [Field k]
    (g : Y ⟶ Spec (CommRingCat.of k)) (n : ℕ) :
    ModuleScalarH g ((pushforward f).obj M) n ≃ₗ[k] ModuleScalarH (f ≫ g) M n := by
  letI _sourceTargetScalars := Module.compHom (ModuleH M n) f.appTop.hom
  refine
    { toAddEquiv := (affinePushforwardModuleHEquiv f M n).toAddEquiv
      map_smul' := ?_ }
  intro r x
  change ModuleH ((pushforward f).obj M) n at x
  have h : structureScalarMap (f ≫ g) r = f.appTop (structureScalarMap g r) := by
    simp [structureScalarMap]
  change affinePushforwardModuleHEquiv f M n
      (structureScalarMap g r • (x : ModuleH ((pushforward f).obj M) n)) =
    structureScalarMap (f ≫ g) r • (affinePushforwardModuleHEquiv f M n x : ModuleH M n)
  rw [h]
  exact (affinePushforwardModuleHEquiv f M n).map_smul (structureScalarMap g r) x

/-- Affine direct-image cohomology comparison commutes with coefficient maps. -/
lemma affinePushforwardCoverHEquiv_naturality {N : X.Modules} [N.IsQuasicoherent]
    (a : M ⟶ N) {ι : Type u} (U : ι → Y.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (hCover : iSup U = ⊤)
    (n : ℕ) (x : ModuleH ((pushforward f).obj M) n) :
    affinePushforwardCoverHEquiv f N U hU hCover n
        (moduleHMap ((pushforward f).map a) n x) =
      moduleHMap a n (affinePushforwardCoverHEquiv f M U hU hCover n x) := by
  let _sourceSeparated : X.IsSeparated := ⟨by
    rw [← terminal.comp_from f]
    infer_instance⟩
  obtain ⟨y, rfl⟩ :=
    (affineCoverCechEquiv ((pushforward f).obj M) U hU hCover n).surjective x
  rw [← affineCoverCechEquiv_naturality]
  simp only [affinePushforwardCoverHEquiv, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_apply]
  rw [PushforwardCech.moduleCechEquiv_naturality]
  exact affineCoverRingCechEquiv_naturality M (fun i ↦ f ⁻¹ᵁ U i)
    (fun i ↦ (hU i).preimage f) (f.iSup_preimage_eq_top hCover) f.appTop.hom a n _

/-- The canonical affine direct-image comparison is natural in quasi-coherent modules. -/
lemma affinePushforwardModuleHEquiv_naturality {N : X.Modules} [N.IsQuasicoherent]
    (a : M ⟶ N) (n : ℕ) (x : ModuleH ((pushforward f).obj M) n) :
    affinePushforwardModuleHEquiv f N n (moduleHMap ((pushforward f).map a) n x) =
      moduleHMap a n (affinePushforwardModuleHEquiv f M n x) :=
  affinePushforwardCoverHEquiv_naturality f M a (fun U : Y.affineOpens ↦ U.1)
    (fun U ↦ U.2) (iSup_affineOpens_eq_top Y) n x

/-- Restriction to any specified base ring retains naturality. -/
lemma affinePushforwardRingHEquiv_naturality {R : Type v} [Ring R]
    (ρ : R →+* Γ(Y, ⊤)) {N : X.Modules} [N.IsQuasicoherent]
    (a : M ⟶ N) (n : ℕ) (x : ModuleH ((pushforward f).obj M) n) :
    affinePushforwardRingHEquiv f N ρ n (moduleHMap ((pushforward f).map a) n x) =
      moduleHMap a n (affinePushforwardRingHEquiv f M ρ n x) :=
  affinePushforwardModuleHEquiv_naturality f M a n x

/-- The field-valued comparison commutes with the existing scalar cohomology maps. -/
lemma affinePushforwardScalarHEquiv_naturality {k : Type u} [Field k]
    (g : Y ⟶ Spec (CommRingCat.of k)) {N : X.Modules} [N.IsQuasicoherent]
    (a : M ⟶ N) (n : ℕ) (x : ModuleScalarH g ((pushforward f).obj M) n) :
    affinePushforwardScalarHEquiv f N g n
        (moduleScalarHMap g ((pushforward f).map a) n x) =
      moduleScalarHMap (f ≫ g) a n (affinePushforwardScalarHEquiv f M g n x) :=
  affinePushforwardModuleHEquiv_naturality f M a n x

/-- The comparison in the existing base-ring cohomology functor's codomain. -/
def affinePushforwardRingHIso {R : Type u} [CommRing R]
    (ρ : R →+* Γ(Y, ⊤)) (n : ℕ) :
    (moduleRingHFunctor ρ n).obj ((pushforward f).obj M) ≅
      (moduleRingHFunctor (f.appTop.hom.comp ρ) n).obj M :=
  (affinePushforwardRingHEquiv f M ρ n).toModuleIso

/-- The bundled comparison commutes with the existing base-ring cohomology functors. -/
lemma affinePushforwardRingHIso_naturality {R : Type u} [CommRing R]
    (ρ : R →+* Γ(Y, ⊤)) {N : X.Modules} [N.IsQuasicoherent]
    (a : M ⟶ N) (n : ℕ) :
    (moduleRingHFunctor ρ n).map ((pushforward f).map a) ≫
        (affinePushforwardRingHIso f N ρ n).hom =
      (affinePushforwardRingHIso f M ρ n).hom ≫
        (moduleRingHFunctor (f.appTop.hom.comp ρ) n).map a := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact affinePushforwardRingHEquiv_naturality f M ρ a n x

/-- Finite generation over the specified base ring is preserved in both directions. -/
theorem affinePushforward_moduleRingH_finite_iff {R : Type u} [CommRing R]
    (ρ : R →+* Γ(Y, ⊤)) (n : ℕ) :
    Module.Finite R (ModuleRingH ρ ((pushforward f).obj M) n) ↔
      Module.Finite R (ModuleRingH (f.appTop.hom.comp ρ) M n) := by
  constructor
  · intro h
    let _finite : Module.Finite R
        ((moduleRingHFunctor ρ n).obj ((pushforward f).obj M)) := h
    exact Module.Finite.equiv (affinePushforwardRingHIso f M ρ n).toLinearEquiv
  · intro h
    let _finite : Module.Finite R
        ((moduleRingHFunctor (f.appTop.hom.comp ρ) n).obj M) := h
    exact Module.Finite.equiv (affinePushforwardRingHIso f M ρ n).symm.toLinearEquiv

/-- Affine direct image also preserves vanishing of the actual module cohomology. -/
theorem affinePushforward_moduleH_subsingleton_iff (n : ℕ) :
    Subsingleton (ModuleH ((pushforward f).obj M) n) ↔ Subsingleton (ModuleH M n) := by
  constructor
  · intro h
    let _vanishing := h
    exact (affinePushforwardModuleHEquiv f M n).symm.injective.subsingleton
  · intro h
    let _vanishing := h
    exact (affinePushforwardModuleHEquiv f M n).injective.subsingleton

end FLT.Mazur.FCurve
