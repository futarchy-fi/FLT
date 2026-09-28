/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Tensor products of module sheaves

The tensor is the sheafification of the sectionwise tensor presheaf. Its maps
represent bilinear maps of sections compatible with restriction. Pure tensors
are mapped into the sheaf by the sheafification unit; they need not generate its
sections globally. Comparison with tensor products of sections on affine opens
requires a separate local comparison theorem.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct
open PresheafOfModulesOfCommRing

universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace FLT.Mazur.FCurve.ModuleSheafTensor

variable {X : Scheme.{u}}

/-- The existing sectionwise tensor, before sheafification. -/
abbrev tensorPresheaf (M N : X.Modules) : X.PresheafOfModules :=
  Monoidal.tensorObj (R := X.presheaf) M.val N.val

/-- Tensor product in the category of actual module sheaves. -/
def tensor (M N : X.Modules) : X.Modules :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj (tensorPresheaf M N)

/-- The canonical map from the sectionwise tensor to the sheaf tensor. -/
def unit (M N : X.Modules) : tensorPresheaf M N ⟶ (tensor M N).val :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app _

/-- A pure tensor of sections, regarded as a section of the tensor sheaf. -/
def pure (M N : X.Modules) (U : X.Opens) (m : Γ(M, U)) (n : Γ(N, U)) :
    Γ(tensor M N, U) :=
  (unit M N).app (.op U) (m ⊗ₜ[Γ(X, U)] n)

/-- Bilinear maps on every open, compatible with every restriction map. -/
structure Bilinear (M N P : X.Modules) where
  /-- The bilinear map on sections of an open. -/
  app (U : X.Opens) : Γ(M, U) →ₗ[Γ(X, U)] Γ(N, U) →ₗ[Γ(X, U)] Γ(P, U)
  /-- Compatibility with restrictions. -/
  naturality {U V : X.Opens} (i : U ⟶ V) (m : Γ(M, V)) (n : Γ(N, V)) :
    app U (M.presheaf.map i.op m) (N.presheaf.map i.op n) =
      P.presheaf.map i.op (app V m n)

@[ext]
lemma Bilinear.ext {M N P : X.Modules} {b c : Bilinear M N P}
    (h : ∀ U m n, b.app U m n = c.app U m n) : b = c := by
  have ha : b.app = c.app := by
    funext U
    ext m n
    exact h U m n
  cases b
  cases c
  cases ha
  rfl

/-- The sectionwise tensor universal property, with restriction compatibility. -/
def Bilinear.lift {M N P : X.Modules} (b : Bilinear M N P) :
    tensorPresheaf M N ⟶ P.val :=
  homMk (fun U ↦ ModuleCat.ofHom (TensorProduct.lift (b.app U.unop))) (fun f ↦ by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro m n
    exact b.naturality f.unop m n)

/-- A tensor-presheaf map determines a natural bilinear map. -/
def ofPresheafHom {M N P : X.Modules} (f : tensorPresheaf M N ⟶ P.val) :
    Bilinear M N P where
  app U := (TensorProduct.lift.equiv (RingHom.id Γ(X, U)) _ _ _).symm (f.app (.op U)).hom
  naturality i m n := PresheafOfModulesOfCommRing.naturality_apply f i.op (m ⊗ₜ n)

/-- Natural bilinear maps are precisely maps from the tensor presheaf. -/
def presheafHomEquiv (M N P : X.Modules) :
    (tensorPresheaf M N ⟶ P.val) ≃ Bilinear M N P where
  toFun := ofPresheafHom
  invFun := Bilinear.lift
  left_inv f := by
    ext1 U
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro m n
    rfl
  right_inv b := by
    ext U m n
    rfl

/-- The universal bilinear property of the sheaf tensor. -/
def homEquiv (M N P : X.Modules) : (tensor M N ⟶ P) ≃ Bilinear M N P :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 X.ringCatSheaf.obj)).trans
    (presheafHomEquiv M N P)

/-- Extension of a bilinear map to the tensor sheaf. -/
def lift {M N P : X.Modules} (b : Bilinear M N P) : tensor M N ⟶ P :=
  (homEquiv M N P).symm b

/-- The universal map evaluates on pure tensors by the specified bilinear map. -/
@[simp]
lemma lift_pure {M N P : X.Modules} (b : Bilinear M N P)
    (U : X.Opens) (m : Γ(M, U)) (n : Γ(N, U)) :
    (lift b).app U (pure M N U m n) = b.app U m n := by
  have h := congrArg (fun c : Bilinear M N P ↦ c.app U m n)
    ((homEquiv M N P).apply_symm_apply b)
  exact h

/-- Maps from the tensor sheaf are determined by their values on local pure tensors. -/
lemma hom_ext {M N P : X.Modules} {f g : tensor M N ⟶ P}
    (h : ∀ U m n, f.app U (pure M N U m n) = g.app U (pure M N U m n)) :
    f = g := by
  apply (homEquiv M N P).injective
  ext U m n
  exact h U m n

/-- Restriction takes pure tensors to pure tensors of the restricted sections. -/
lemma pure_restrict (M N : X.Modules) {U V : X.Opens} (i : U ⟶ V)
    (m : Γ(M, V)) (n : Γ(N, V)) :
    (tensor M N).presheaf.map i.op (pure M N V m n) =
      pure M N U (M.presheaf.map i.op m) (N.presheaf.map i.op n) :=
  (PresheafOfModulesOfCommRing.naturality_apply (unit M N) i.op (m ⊗ₜ n)).symm

/-- The canonical bilinear pairing into the tensor sheaf. -/
def pairing (M N : X.Modules) : Bilinear M N (tensor M N) :=
  ofPresheafHom (unit M N)

@[simp]
lemma pairing_apply (M N : X.Modules) (U : X.Opens) (m : Γ(M, U)) (n : Γ(N, U)) :
    (pairing M N).app U m n = pure M N U m n := rfl

/-- Existence and uniqueness in the bilinear universal property. -/
theorem existsUnique_lift {M N P : X.Modules} (b : Bilinear M N P) :
    ∃! f : tensor M N ⟶ P, ∀ U m n, f.app U (pure M N U m n) = b.app U m n := by
  refine ⟨lift b, lift_pure b, fun f hf ↦ ?_⟩
  apply hom_ext
  intro U m n
  rw [hf, lift_pure]

/-- Tensoring two morphisms of sheaves. -/
def map {M N M' N' : X.Modules} (f : M ⟶ M') (g : N ⟶ N') :
    tensor M N ⟶ tensor M' N' :=
  lift (ofPresheafHom (Monoidal.tensorHom f.val g.val ≫ unit M' N'))

@[simp]
lemma map_pure {M N M' N' : X.Modules} (f : M ⟶ M') (g : N ⟶ N')
    (U : X.Opens) (m : Γ(M, U)) (n : Γ(N, U)) :
    (map f g).app U (pure M N U m n) = pure M' N' U (f.app U m) (g.app U n) := by
  rw [map, lift_pure]
  rfl

@[simp]
lemma map_id (M N : X.Modules) : map (𝟙 M) (𝟙 N) = 𝟙 (tensor M N) := by
  apply hom_ext
  intro U m n
  simp

@[reassoc]
lemma map_comp {M₁ M₂ M₃ N₁ N₂ N₃ : X.Modules}
    (f : M₁ ⟶ M₂) (f' : M₂ ⟶ M₃) (g : N₁ ⟶ N₂) (g' : N₂ ⟶ N₃) :
    map (f ≫ f') (g ≫ g') = map f g ≫ map f' g' := by
  apply hom_ext
  intro U m n
  simp

/-- The tensor construction respects isomorphisms in both variables. -/
def congr {M N M' N' : X.Modules} (e : M ≅ M') (f : N ≅ N') :
    tensor M N ≅ tensor M' N' where
  hom := map e.hom f.hom
  inv := map e.inv f.inv
  hom_inv_id := by rw [← map_comp]; simp
  inv_hom_id := by rw [← map_comp]; simp

/-- If the tensor presheaf is already a sheaf, the canonical comparison is invertible. -/
lemma isIso_unit_of_isSheaf (M N : X.Modules)
    (h : Presheaf.IsSheaf (Opens.grothendieckTopology X)
      (tensorPresheaf M N).presheaf) : IsIso (unit M N) := by
  have : IsIso ((PresheafOfModules.toPresheaf _).map (unit M N)) := by
    change IsIso (CategoryTheory.toSheafify _ (tensorPresheaf M N).presheaf)
    exact CategoryTheory.isIso_toSheafify _ h
  exact isIso_of_reflects_iso _ (PresheafOfModules.toPresheaf _)

/-- Tensoring the structure module with a sheaf needs no further sheafification. -/
lemma unit_tensor_isSheaf (M : X.Modules) :
    Presheaf.IsSheaf (Opens.grothendieckTopology X)
      (tensorPresheaf (SheafOfModules.unit X.ringCatSheaf) M).presheaf := by
  let e : tensorPresheaf (SheafOfModules.unit X.ringCatSheaf) M ≅ M.val :=
    MonoidalCategory.leftUnitor (show PresheafOfModulesOfCommRing X.presheaf from M.val)
  exact (Presheaf.isSheaf_of_iso_iff ((PresheafOfModules.toPresheaf _).mapIso e)).mpr
    M.isSheaf

/-- The structure module is a left unit for the constructed tensor. -/
def leftUnitor (M : X.Modules) :
    tensor (SheafOfModules.unit X.ringCatSheaf) M ≅ M := by
  let e : tensorPresheaf (SheafOfModules.unit X.ringCatSheaf) M ≅ M.val :=
    MonoidalCategory.leftUnitor (show PresheafOfModulesOfCommRing X.presheaf from M.val)
  let := isIso_unit_of_isSheaf (SheafOfModules.unit X.ringCatSheaf) M
    (unit_tensor_isSheaf M)
  exact (SheafOfModules.fullyFaithfulForget X.ringCatSheaf).preimageIso
    ((asIso (unit (SheafOfModules.unit X.ringCatSheaf) M)).symm ≪≫ e)

/-- The left unit comparison evaluates a pure tensor by scalar multiplication. -/
@[simp]
lemma leftUnitor_pure (M : X.Modules) (U : X.Opens) (r : Γ(X, U)) (m : Γ(M, U)) :
    (leftUnitor M).hom.app U (pure (SheafOfModules.unit X.ringCatSheaf) M U r m) =
      r • m := by
  let := isIso_unit_of_isSheaf (SheafOfModules.unit X.ringCatSheaf) M
    (unit_tensor_isSheaf M)
  have h := congrArg (fun f ↦ f.app (.op U))
    (IsIso.hom_inv_id (unit (SheafOfModules.unit X.ringCatSheaf) M))
  have he := congrArg (fun f ↦ (ModuleCat.Hom.hom f) (r ⊗ₜ[Γ(X, U)] m)) h
  change (MonoidalCategory.leftUnitor
    (show PresheafOfModulesOfCommRing X.presheaf from M.val)).hom.app (.op U)
    ((inv (unit (SheafOfModules.unit X.ringCatSheaf) M)).app (.op U)
      ((unit (SheafOfModules.unit X.ringCatSheaf) M).app (.op U) (r ⊗ₜ m))) = _
  rw [show (inv (unit (SheafOfModules.unit X.ringCatSheaf) M)).app (.op U)
      ((unit (SheafOfModules.unit X.ringCatSheaf) M).app (.op U) (r ⊗ₜ m)) =
        r ⊗ₜ m from he]
  rfl

end FLT.Mazur.FCurve.ModuleSheafTensor
