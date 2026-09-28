/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSheafTensorTilde

/-!
# Tensor sections on affine opens

For quasi-coherent module sheaves the canonical tensor comparison is invertible
on every affine open. In particular this applies to locally free sheaves, without
requiring their modules of sections to be free.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite

universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace FLT.Mazur.FCurve.ModuleSheafTensor

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

/-- Evaluating the tilde isomorphism at the top gives the coordinate-ring tensor map. -/
instance affineUnit_isIso {R : CommRingCat.{u}} (M N : (Spec R).Modules)
    [M.IsQuasicoherent] [N.IsQuasicoherent] : IsIso (affineUnit M N) := by
  have h : affineUnit M N = (tilde.isoTop (affineTensorModule M N)).hom ≫
      moduleSpecΓFunctor.map (affineTildeComparison M N) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro t
    exact (affineTildeComparison_top M N t).symm
  rw [h]
  infer_instance

/-- The canonical comparison is invertible on each basic open of a spectrum. -/
lemma unit_basic_bijective {R : CommRingCat.{u}} (M N : (Spec R).Modules)
    [M.IsQuasicoherent] [N.IsQuasicoherent] (f : R) :
    Function.Bijective ((unit M N).app (op (PrimeSpectrum.basicOpen f))) := by
  let e := (basicTensorLinearEquiv M N f).trans
    (sectionsCongr (affineTildeIso M N) (PrimeSpectrum.basicOpen f))
  have h : ∀ t, (unit M N).app (op (PrimeSpectrum.basicOpen f)) t = e t := by
    intro t
    exact (LinearMap.congr_fun (affineTildeComparison_basicTensorEquiv M N f) t).symm
  change Function.Bijective (fun t ↦ (unit M N).app (op (PrimeSpectrum.basicOpen f)) t)
  rw [funext h]
  exact e.bijective

/-- The top open of a spectrum is the basic open of one. -/
lemma unit_spec_top_bijective {R : CommRingCat.{u}} (M N : (Spec R).Modules)
    [M.IsQuasicoherent] [N.IsQuasicoherent] :
    Function.Bijective ((unit M N).app (op ⊤)) := by
  have h := unit_basic_bijective M N (1 : R)
  have he : PrimeSpectrum.basicOpen (1 : R) = (⊤ : (Spec R).Opens) :=
    PrimeSpectrum.basicOpen_one
  rw [he] at h
  exact h

/-- Restriction identifies section modules semilinearly over the open-immersion ring iso. -/
def restrictSectionsEquiv {X Y : Scheme.{u}} (M : X.Modules)
    (j : Y ⟶ X) [IsOpenImmersion j] (U : Y.Opens) :
    Γ(M.restrict j, U) ≃ₛₗ[((j.appIso U).commRingCatIsoToRingEquiv.symm :
      Γ(Y, U) →+* Γ(X, j ''ᵁ U))] Γ(M, j ''ᵁ U) where
  toFun := (M.restrictAppIso j U).hom
  invFun := (M.restrictAppIso j U).inv
  left_inv := fun _ ↦ rfl
  right_inv := fun _ ↦ rfl
  map_add' := map_add _
  map_smul' := fun _ _ ↦ rfl

/-- Invertibility of the canonical comparison transports along an open immersion. -/
lemma unit_image_bijective {X Y : Scheme.{u}} (M N : X.Modules)
    (j : Y ⟶ X) [IsOpenImmersion j] (U : Y.Opens)
    (h : Function.Bijective ((unit (M.restrict j) (N.restrict j)).app (op U))) :
    Function.Bijective ((unit M N).app (op (j ''ᵁ U))) := by
  let e := TensorProduct.congr (restrictSectionsEquiv M j U) (restrictSectionsEquiv N j U)
  let t := (sectionsCongr (restrictIso M N j).symm U).trans
    (restrictSectionsEquiv (tensor M N) j U)
  have he : ∀ z, (unit M N).app (op (j ''ᵁ U)) (e z) =
      t ((unit (M.restrict j) (N.restrict j)).app (op U) z) := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul m n => exact (restrictComparison_pure M N j U m n).symm
    | add z z' hz hz' => simpa only [map_add] using congrArg₂ (· + ·) hz hz'
  have hb : Function.Bijective
      (fun z ↦ (unit M N).app (op (j ''ᵁ U)) (e z)) := by
    rw [funext he]
    exact t.bijective.comp h
  exact (Function.Bijective.of_comp_iff _ e.bijective).mp hb

/-- The canonical tensor comparison is invertible on any affine open. -/
lemma unit_affine_bijective {X : Scheme.{u}} (M N : X.Modules)
    [M.IsQuasicoherent] [N.IsQuasicoherent] (V : X.Opens) (hV : IsAffineOpen V) :
    Function.Bijective ((unit M N).app (op V)) := by
  have h := unit_image_bijective M N hV.fromSpec ⊤
    (unit_spec_top_bijective (M.restrict hV.fromSpec) (N.restrict hV.fromSpec))
  have he : hV.fromSpec ''ᵁ ⊤ = V := by simp
  rw [he] at h
  exact h

/-- The canonical tensor equivalence for quasi-coherent sheaves on an affine open. -/
def affineSectionsEquiv {X : Scheme.{u}} (M N : X.Modules)
    [M.IsQuasicoherent] [N.IsQuasicoherent] (V : X.Opens) (hV : IsAffineOpen V) :
    Γ(M, V) ⊗[Γ(X, V)] Γ(N, V) ≃ₗ[Γ(X, V)] Γ(tensor M N, V) :=
  LinearEquiv.ofBijective ((unit M N).app (op V)).hom (unit_affine_bijective M N V hV)

/-- The affine equivalence is the original pure-section map. -/
@[simp]
lemma affineSectionsEquiv_tmul {X : Scheme.{u}} (M N : X.Modules)
    [M.IsQuasicoherent] [N.IsQuasicoherent] (V : X.Opens) (hV : IsAffineOpen V)
    (m : Γ(M, V)) (n : Γ(N, V)) :
    affineSectionsEquiv M N V hV (m ⊗ₜ n) = pure M N V m n := rfl

/-- Its inverse recovers the original simple tensor. -/
@[simp]
lemma affineSectionsEquiv_symm_pure {X : Scheme.{u}} (M N : X.Modules)
    [M.IsQuasicoherent] [N.IsQuasicoherent] (V : X.Opens) (hV : IsAffineOpen V)
    (m : Γ(M, V)) (n : Γ(N, V)) :
    (affineSectionsEquiv M N V hV).symm (pure M N V m n) = m ⊗ₜ n :=
  (affineSectionsEquiv M N V hV).symm_apply_apply (m ⊗ₜ n)

/-- Locally free sheaves, of any rank, have the affine tensor section equivalence. -/
def locallyFreeAffineSectionsEquiv {X : Scheme.{u}} (M N : X.Modules)
    [M.IsLocallyFree] [N.IsLocallyFree] (V : X.Opens) (hV : IsAffineOpen V) :
    Γ(M, V) ⊗[Γ(X, V)] Γ(N, V) ≃ₗ[Γ(X, V)] Γ(tensor M N, V) :=
  affineSectionsEquiv M N V hV

@[simp]
lemma locallyFreeAffineSectionsEquiv_tmul {X : Scheme.{u}} (M N : X.Modules)
    [M.IsLocallyFree] [N.IsLocallyFree] (V : X.Opens) (hV : IsAffineOpen V)
    (m : Γ(M, V)) (n : Γ(N, V)) :
    locallyFreeAffineSectionsEquiv M N V hV (m ⊗ₜ n) = pure M N V m n := rfl

@[simp]
lemma locallyFreeAffineSectionsEquiv_symm_pure {X : Scheme.{u}} (M N : X.Modules)
    [M.IsLocallyFree] [N.IsLocallyFree] (V : X.Opens) (hV : IsAffineOpen V)
    (m : Γ(M, V)) (n : Γ(N, V)) :
    (locallyFreeAffineSectionsEquiv M N V hV).symm (pure M N V m n) = m ⊗ₜ n :=
  affineSectionsEquiv_symm_pure M N V hV m n

end FLT.Mazur.FCurve.ModuleSheafTensor
