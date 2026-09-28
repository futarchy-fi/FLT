/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSheafTensorRestrict
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.RingTheory.Localization.BaseChange

/-!
# Localization of affine tensor sections

For actual quasi-coherent module sheaves on a spectrum, the tensor of sections on
any basic open is the localization of the tensor of global sections. This gives
a canonical comparison with the tilde of that global tensor, including its
values on restricted pure tensors. No freeness of the section modules is used.

The tilde adjunction gives a canonical map to the existing sheaf tensor, and its
composites with the basic-open equivalences equal the sheafification unit. Proving
this map invertible, then transporting to every affine open, remains a separate
sheafification argument.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct
open PrimeSpectrum

universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace FLT.Mazur.FCurve.ModuleSheafTensor

variable {R : CommRingCat.{u}}

/-- Restriction from global sections, with scalars in the affine coordinate ring. -/
def affineRestriction (M : (Spec R).Modules) (f : R) :
    Γ(M, ⊤) →ₗ[R] Γ(M, basicOpen f) :=
  ((modulesSpecToSheaf.obj M).presheaf.map (homOfLE (show basicOpen f ≤ ⊤ from le_top)).op).hom

/-- Quasi-coherent restriction to a basic open is module localization. -/
instance affineRestriction_isLocalized (M : (Spec R).Modules) [M.IsQuasicoherent]
    (f : R) : IsLocalizedModule (.powers f) (affineRestriction M f) :=
  (isIso_fromTildeΓ_iff_isLocalizing M).mp inferInstance f

/-- Change from the basic-open scalar ring to the affine coordinate ring. -/
def basicTensorScalars (M N : (Spec R).Modules) (f : R) :
    Γ(M, basicOpen f) ⊗[Γ(Spec R, basicOpen f)] Γ(N, basicOpen f) ≃ₗ[R]
      Γ(M, basicOpen f) ⊗[R] Γ(N, basicOpen f) :=
  (IsLocalization.moduleTensorEquiv (.powers f) (Γ(Spec R, basicOpen f))
    (Γ(M, basicOpen f)) (Γ(N, basicOpen f))).restrictScalars R

@[simp]
lemma basicTensorScalars_tmul (M N : (Spec R).Modules) (f : R)
    (m : Γ(M, basicOpen f)) (n : Γ(N, basicOpen f)) :
    basicTensorScalars M N f (m ⊗ₜ n) = m ⊗ₜ[R] n := rfl

@[simp]
lemma basicTensorScalars_symm_tmul (M N : (Spec R).Modules) (f : R)
    (m : Γ(M, basicOpen f)) (n : Γ(N, basicOpen f)) :
    (basicTensorScalars M N f).symm (m ⊗ₜ[R] n) = m ⊗ₜ n := rfl

/-- The tensor of global restrictions, with the correct basic-open scalars. -/
def affineTensorRestriction (M N : (Spec R).Modules) (f : R) :
    Γ(M, ⊤) ⊗[R] Γ(N, ⊤) →ₗ[R]
      Γ(M, basicOpen f) ⊗[Γ(Spec R, basicOpen f)] Γ(N, basicOpen f) :=
  (basicTensorScalars M N f).symm.toLinearMap.comp
    (TensorProduct.map (affineRestriction M f) (affineRestriction N f))

@[simp]
lemma affineTensorRestriction_tmul (M N : (Spec R).Modules) (f : R)
    (m : Γ(M, ⊤)) (n : Γ(N, ⊤)) :
    affineTensorRestriction M N f (m ⊗ₜ[R] n) =
      affineRestriction M f m ⊗ₜ affineRestriction N f n := rfl

/-- Tensoring quasi-coherent restrictions again gives module localization. -/
instance affineTensorRestriction_isLocalized (M N : (Spec R).Modules)
    [M.IsQuasicoherent] [N.IsQuasicoherent] (f : R) :
    IsLocalizedModule (.powers f) (affineTensorRestriction M N f) :=
  IsLocalizedModule.of_linearEquiv (.powers f)
    (TensorProduct.map (affineRestriction M f) (affineRestriction N f))
    (basicTensorScalars M N f).symm

/-- The coordinate-ring tensor of the actual global section modules. -/
abbrev affineTensorModule (M N : (Spec R).Modules) : ModuleCat R :=
  ModuleCat.of R (Γ(M, ⊤) ⊗[R] Γ(N, ⊤))

private lemma tilde_toOpen_isLocalized (T : ModuleCat R) (f : R) :
    IsLocalizedModule (.powers f) (tilde.toOpen T (basicOpen f)).hom :=
  inferInstanceAs (IsLocalizedModule.Away f (tilde.toOpen T (basicOpen f)).hom)

/-- The canonical localization into tilde, with explicit section-module scalars. -/
def affineTensorToOpen (M N : (Spec R).Modules) (f : R) :
    Γ(M, ⊤) ⊗[R] Γ(N, ⊤) →ₗ[R]
      Γ(tilde (affineTensorModule M N), basicOpen f) :=
  (tilde.toOpen (affineTensorModule M N) (basicOpen f)).hom

/-- Tilde localization for the global tensor. -/
instance affineTensorToOpen_isLocalized (M N : (Spec R).Modules) (f : R) :
    IsLocalizedModule (.powers f) (affineTensorToOpen M N f) :=
  tilde_toOpen_isLocalized (affineTensorModule M N) f

/-- Basic-open tensor sections agree with the tilde of the global tensor. -/
def basicTensorEquiv (M N : (Spec R).Modules)
    [M.IsQuasicoherent] [N.IsQuasicoherent] (f : R) :
    Γ(M, basicOpen f) ⊗[Γ(Spec R, basicOpen f)] Γ(N, basicOpen f) ≃ₗ[R]
      Γ(tilde (R := R) (affineTensorModule M N), basicOpen f) :=
  IsLocalizedModule.linearEquiv (.powers f) (affineTensorRestriction M N f)
    (affineTensorToOpen M N f)

/-- The comparison agrees with the canonical localization maps. -/
@[simp]
lemma basicTensorEquiv_restriction (M N : (Spec R).Modules)
    [M.IsQuasicoherent] [N.IsQuasicoherent] (f : R)
    (t : Γ(M, ⊤) ⊗[R] Γ(N, ⊤)) :
    basicTensorEquiv M N f (affineTensorRestriction M N f t) =
      tilde.toOpen (R := R) (affineTensorModule M N) (basicOpen f) t :=
  IsLocalizedModule.linearEquiv_apply (.powers f)
    (affineTensorRestriction M N f) (affineTensorToOpen M N f) t

/-- Restricted pure tensors correspond to the same global pure tensor in tilde. -/
@[simp]
lemma basicTensorEquiv_tmul (M N : (Spec R).Modules)
    [M.IsQuasicoherent] [N.IsQuasicoherent] (f : R)
    (m : Γ(M, ⊤)) (n : Γ(N, ⊤)) :
    basicTensorEquiv M N f
      (affineRestriction M f m ⊗ₜ affineRestriction N f n) =
      tilde.toOpen (R := R) (affineTensorModule M N) (basicOpen f) (m ⊗ₜ[R] n) :=
  basicTensorEquiv_restriction M N f (m ⊗ₜ[R] n)

/-- The inverse comparison recovers restricted pure tensors. -/
@[simp]
lemma basicTensorEquiv_symm_tmul (M N : (Spec R).Modules)
    [M.IsQuasicoherent] [N.IsQuasicoherent] (f : R)
    (m : Γ(M, ⊤)) (n : Γ(N, ⊤)) :
    (basicTensorEquiv M N f).symm
      (tilde.toOpen (R := R) (affineTensorModule M N) (basicOpen f) (m ⊗ₜ[R] n)) =
      affineRestriction M f m ⊗ₜ affineRestriction N f n :=
  (basicTensorEquiv M N f).symm_apply_eq.mpr (basicTensorEquiv_tmul M N f m n).symm

/-- The basic-open comparison is linear over the ring of that open. -/
def basicTensorLinearEquiv (M N : (Spec R).Modules)
    [M.IsQuasicoherent] [N.IsQuasicoherent] (f : R) :
    Γ(M, basicOpen f) ⊗[Γ(Spec R, basicOpen f)] Γ(N, basicOpen f)
      ≃ₗ[Γ(Spec R, basicOpen f)] Γ(tilde (affineTensorModule M N), basicOpen f) :=
  (basicTensorEquiv M N f).extendScalarsOfIsLocalization
    (.powers f) (Γ(Spec R, basicOpen f))

/-- Restriction between tensor sections on basic opens, viewed over `R`. -/
def basicTensorRestrict (M N : (Spec R).Modules) {f g : R}
    (i : basicOpen g ⟶ basicOpen f) :
    Γ(M, basicOpen f) ⊗[Γ(Spec R, basicOpen f)] Γ(N, basicOpen f) →ₗ[R]
      Γ(M, basicOpen g) ⊗[Γ(Spec R, basicOpen g)] Γ(N, basicOpen g) :=
  (basicTensorScalars M N g).symm.toLinearMap.comp
    ((TensorProduct.map ((modulesSpecToSheaf.obj M).presheaf.map i.op).hom
      ((modulesSpecToSheaf.obj N).presheaf.map i.op).hom).comp
        (basicTensorScalars M N f).toLinearMap)

@[simp]
lemma basicTensorRestrict_tmul (M N : (Spec R).Modules) {f g : R}
    (i : basicOpen g ⟶ basicOpen f)
    (m : Γ(M, basicOpen f)) (n : Γ(N, basicOpen f)) :
    basicTensorRestrict M N i (m ⊗ₜ n) =
      (show Γ(M, basicOpen g) from M.presheaf.map i.op m) ⊗ₜ
        (show Γ(N, basicOpen g) from N.presheaf.map i.op n) := rfl

/-- The basic-open tensor restriction is the existing tensor-presheaf restriction. -/
lemma basicTensorRestrict_eq (M N : (Spec R).Modules) {f g : R}
    (i : basicOpen g ⟶ basicOpen f)
    (t : Γ(M, basicOpen f) ⊗[Γ(Spec R, basicOpen f)] Γ(N, basicOpen f)) :
    basicTensorRestrict M N i t = (tensorPresheaf M N).map i.op t := by
  induction t using TensorProduct.inductionOn with
  | tmul m n => rfl
  | add t t' ht ht' => simpa only [map_add] using congrArg₂ (· + ·) ht ht'

/-- Restricting the global tensor through a basic open gives direct restriction. -/
lemma basicTensorRestrict_global (M N : (Spec R).Modules) {f g : R}
    (i : basicOpen g ⟶ basicOpen f) :
    (basicTensorRestrict M N i).comp (affineTensorRestriction M N f) =
      affineTensorRestriction M N g := by
  ext m n
  change (show Γ(M, basicOpen g) from M.presheaf.map i.op (M.presheaf.map _ m)) ⊗ₜ
    (show Γ(N, basicOpen g) from N.presheaf.map i.op (N.presheaf.map _ n)) = _
  simp only [← Functor.map_comp_apply]
  rfl

/-- The localization comparison commutes with every inclusion of basic opens. -/
lemma basicTensorEquiv_naturality (M N : (Spec R).Modules)
    [M.IsQuasicoherent] [N.IsQuasicoherent] {f g : R}
    (i : basicOpen g ⟶ basicOpen f) :
    ((modulesSpecToSheaf.obj (tilde (affineTensorModule M N))).presheaf.map i.op).hom.comp
        (basicTensorEquiv M N f).toLinearMap =
      (basicTensorEquiv M N g).toLinearMap.comp (basicTensorRestrict M N i) := by
  apply IsLocalizedModule.ext (.powers f) (affineTensorRestriction M N f)
  · rw [Subtype.forall]
    change Submonoid.powers f ≤ (IsUnit.submonoid _).comap _
    simp only [Submonoid.powers_le, Submonoid.mem_comap, IsUnit.mem_submonoid_iff]
    exact (tilde (affineTensorModule M N)).isUnit_algebraMap_end_of_le_basicOpen f i.le
  · simp only [LinearMap.comp_assoc]
    erw [basicTensorRestrict_global]
    apply LinearMap.ext
    intro t
    change ((modulesSpecToSheaf.obj (tilde (affineTensorModule M N))).presheaf.map i.op
      (basicTensorEquiv M N f (affineTensorRestriction M N f t))) =
      basicTensorEquiv M N g (affineTensorRestriction M N g t)
    rw [basicTensorEquiv_restriction, basicTensorEquiv_restriction]
    exact congrArg (fun h ↦ h t) (tilde.toOpen_res (affineTensorModule M N) _ _ i)

/-- The existing pure pairing on global sections, with coordinate-ring scalars. -/
def affineUnit (M N : (Spec R).Modules) :
    affineTensorModule M N ⟶ moduleSpecΓFunctor.obj (tensor M N) :=
  show ModuleCat.of R (Γ(M, ⊤) ⊗[R] Γ(N, ⊤)) ⟶ ModuleCat.of R Γ(tensor M N, ⊤) from
    ModuleCat.ofHom (TensorProduct.lift (((pairing M N).app ⊤).restrictScalars₁₂ R R))

@[simp]
lemma affineUnit_tmul (M N : (Spec R).Modules) (m : Γ(M, ⊤)) (n : Γ(N, ⊤)) :
    affineUnit M N (m ⊗ₜ[R] n) = pure M N ⊤ m n := rfl

/-- The canonical morphism from the tilde of the global tensor to the sheaf tensor. -/
def affineTildeComparison (M N : (Spec R).Modules) :
    tilde (affineTensorModule M N) ⟶ tensor M N :=
  (tilde.adjunction.homEquiv _ _).symm (affineUnit M N)

/-- The adjunction comparison recovers the existing global tensor unit. -/
lemma affineTildeComparison_top (M N : (Spec R).Modules)
    (t : affineTensorModule M N) :
    (affineTildeComparison M N).app ⊤ (tilde.toOpen (affineTensorModule M N) ⊤ t) =
      affineUnit M N t := by
  have h := (tilde.adjunction.homEquiv _ _).apply_symm_apply (affineUnit M N)
  exact congrArg (fun k ↦ k t) h

/-- On every open, the comparison takes localized global tensors to restricted sections. -/
lemma affineTildeComparison_toOpen (M N : (Spec R).Modules) (U : (Spec R).Opens)
    (t : affineTensorModule M N) :
    (affineTildeComparison M N).app U (tilde.toOpen (affineTensorModule M N) U t) =
      (tensor M N).presheaf.map U.leTop.op (affineUnit M N t) := by
  have ht := congrArg (fun k ↦ k t)
    (tilde.toOpen_res (affineTensorModule M N) ⊤ U U.leTop)
  change (tilde (affineTensorModule M N)).presheaf.map U.leTop.op
    (tilde.toOpen (affineTensorModule M N) ⊤ t) = _ at ht
  rw [← ht]
  have h := ConcreteCategory.congr_hom
    ((affineTildeComparison M N).mapPresheaf.naturality U.leTop.op)
    (tilde.toOpen (affineTensorModule M N) ⊤ t)
  change (affineTildeComparison M N).app U _ =
    (tensor M N).presheaf.map U.leTop.op
      ((affineTildeComparison M N).app ⊤ _) at h
  exact h.trans (congrArg ((tensor M N).presheaf.map U.leTop.op)
    (affineTildeComparison_top M N t))

/-- The localization comparison intertwines the actual sheafification unit. -/
lemma affineTildeComparison_basicTensorEquiv (M N : (Spec R).Modules)
    [M.IsQuasicoherent] [N.IsQuasicoherent] (f : R) :
    ((show Γ(tilde (affineTensorModule M N), basicOpen f) →ₗ[Γ(Spec R, basicOpen f)]
      Γ(tensor M N, basicOpen f) from
        ((affineTildeComparison M N).val.app (.op (basicOpen f))).hom).restrictScalars R).comp
        (basicTensorEquiv M N f).toLinearMap =
      (show Γ(M, basicOpen f) ⊗[Γ(Spec R, basicOpen f)] Γ(N, basicOpen f)
        →ₗ[Γ(Spec R, basicOpen f)] Γ(tensor M N, basicOpen f) from
          ((unit M N).app (.op (basicOpen f))).hom).restrictScalars R := by
  apply IsLocalizedModule.ext (.powers f) (affineTensorRestriction M N f)
  · rw [Subtype.forall]
    change Submonoid.powers f ≤ (IsUnit.submonoid _).comap _
    simp only [Submonoid.powers_le, Submonoid.mem_comap, IsUnit.mem_submonoid_iff]
    exact (tensor M N).isUnit_algebraMap_end_of_le_basicOpen f le_rfl
  · ext m n
    change (affineTildeComparison M N).app (basicOpen f)
      (basicTensorEquiv M N f (affineTensorRestriction M N f (m ⊗ₜ[R] n))) = _
    rw [basicTensorEquiv_restriction, affineTildeComparison_toOpen, affineUnit_tmul,
      pure_restrict]
    rfl

/-- The composite comparison gives the existing pure section for arbitrary local factors. -/
@[simp]
lemma affineTildeComparison_basicTensorLinearEquiv_tmul (M N : (Spec R).Modules)
    [M.IsQuasicoherent] [N.IsQuasicoherent] (f : R)
    (m : Γ(M, basicOpen f)) (n : Γ(N, basicOpen f)) :
    (affineTildeComparison M N).app (basicOpen f)
      (basicTensorLinearEquiv M N f (m ⊗ₜ n)) = pure M N (basicOpen f) m n := by
  exact LinearMap.congr_fun (affineTildeComparison_basicTensorEquiv M N f) (m ⊗ₜ n)

end FLT.Mazur.FCurve.ModuleSheafTensor
