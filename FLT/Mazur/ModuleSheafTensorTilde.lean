/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSheafTensorAffine
public import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-!
# Affine tensor comparison through sheafification

The basic-open tensor equivalences extend to a map into the tilde sheaf by
cover density. The additive sheafification universal property then constructs
an inverse to the existing affine comparison. Reflecting invertibility through
the forgetful functor gives the comparison for actual module sheaves.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry PrimeSpectrum Opposite

universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace FLT.Mazur.FCurve.ModuleSheafTensor

variable {R : CommRingCat.{u}} (M N : (Spec R).Modules)
variable [M.IsQuasicoherent] [N.IsQuasicoherent]

/-- The underlying additive comparison on the category of basic opens. -/
def basicTensorComparison :
    (inducedFunctor (basicOpen (R := R))).op ⋙ (tensorPresheaf M N).presheaf ⟶
      (inducedFunctor (basicOpen (R := R))).op ⋙ (tilde (affineTensorModule M N)).presheaf where
  app f := AddCommGrpCat.ofHom (basicTensorLinearEquiv M N f.unop).toAddMonoidHom
  naturality {f g} i := by
    ext t
    exact ((LinearMap.congr_fun
      (basicTensorEquiv_naturality M N ((inducedFunctor (basicOpen (R := R))).map i.unop)) t).trans
        (congrArg (basicTensorEquiv M N g.unop)
          (basicTensorRestrict_eq M N ((inducedFunctor (basicOpen (R := R))).map i.unop) t))).symm

/-- Extend the tensor-presheaf comparison from the cover-dense basic-open basis. -/
def tensorToTilde :
    (tensorPresheaf M N).presheaf ⟶ (tilde (affineTensorModule M N)).presheaf :=
  TopCat.Sheaf.restrictHomEquivHom (tensorPresheaf M N).presheaf
    ((SheafOfModules.toSheaf _).obj (tilde (affineTensorModule M N)))
    PrimeSpectrum.isBasis_basic_opens (basicTensorComparison M N)

/-- On basic opens the extension is the original localization equivalence. -/
@[simp]
lemma tensorToTilde_basic (f : R) :
    (tensorToTilde M N).app (op (basicOpen f)) =
      AddCommGrpCat.ofHom (basicTensorLinearEquiv M N f).toAddMonoidHom :=
  TopCat.Sheaf.extend_hom_app _ _ PrimeSpectrum.isBasis_basic_opens _ f

/-- The extended comparison still factors the existing sheafification unit. -/
lemma tensorToTilde_comparison :
    tensorToTilde M N ≫ (affineTildeComparison M N).mapPresheaf =
      (PresheafOfModules.toPresheaf _).map (unit M N) := by
  apply TopCat.Sheaf.hom_ext (tensorPresheaf M N).presheaf
    ((SheafOfModules.toSheaf _).obj (tensor M N)) PrimeSpectrum.isBasis_basic_opens
  intro f
  ext t
  change (affineTildeComparison M N).app (basicOpen f)
    ((tensorToTilde M N).app (op (basicOpen f)) t) = _
  rw [tensorToTilde_basic]
  exact LinearMap.congr_fun (affineTildeComparison_basicTensorEquiv M N f) t

/-- Extend to the additive sheaf tensor by the sheafification universal property. -/
def tensorToTildeSheaf :
    (SheafOfModules.toSheaf _).obj (tensor M N) ⟶
      (SheafOfModules.toSheaf _).obj (tilde (affineTensorModule M N)) :=
  ((CategoryTheory.sheafificationAdjunction
    (Opens.grothendieckTopology (Spec R)) AddCommGrpCat).homEquiv _ _).symm
      (tensorToTilde M N)

/-- The sheafified map agrees with the extended map on the tensor presheaf. -/
lemma unit_tensorToTildeSheaf :
    (PresheafOfModules.toPresheaf _).map (unit M N) ≫
      (tensorToTildeSheaf M N).hom = tensorToTilde M N := by
  exact ((CategoryTheory.sheafificationAdjunction
    (Opens.grothendieckTopology (Spec R)) AddCommGrpCat).homEquiv (tensorPresheaf M N).presheaf
      ((SheafOfModules.toSheaf _).obj (tilde (affineTensorModule M N)))).apply_symm_apply
      (tensorToTilde M N)

/-- The additive extension is a right inverse of the original comparison. -/
lemma tensorToTildeSheaf_comparison :
    tensorToTildeSheaf M N ≫
      (SheafOfModules.toSheaf _).map (affineTildeComparison M N) = 𝟙 _ := by
  apply ((CategoryTheory.sheafificationAdjunction
    (Opens.grothendieckTopology (Spec R)) AddCommGrpCat).homEquiv _ _).injective
  change (PresheafOfModules.toPresheaf _).map (unit M N) ≫
    ((tensorToTildeSheaf M N).hom ≫ (affineTildeComparison M N).mapPresheaf) =
      (PresheafOfModules.toPresheaf _).map (unit M N) ≫ 𝟙 _
  rw [← Category.assoc, unit_tensorToTildeSheaf, tensorToTilde_comparison, Category.comp_id]

/-- The additive extension is also a left inverse, as checked on the basis. -/
lemma comparison_tensorToTildeSheaf :
    (SheafOfModules.toSheaf _).map (affineTildeComparison M N) ≫
      tensorToTildeSheaf M N = 𝟙 _ := by
  apply Sheaf.hom_ext
  apply TopCat.Sheaf.hom_ext (tilde (affineTensorModule M N)).presheaf
    ((SheafOfModules.toSheaf _).obj (tilde (affineTensorModule M N)))
    PrimeSpectrum.isBasis_basic_opens
  intro f
  ext t
  obtain ⟨s, rfl⟩ := (basicTensorLinearEquiv M N f).surjective t
  have hc := LinearMap.congr_fun (affineTildeComparison_basicTensorEquiv M N f) s
  change (tensorToTildeSheaf M N).hom.app (op (basicOpen f))
    ((affineTildeComparison M N).app (basicOpen f)
      (basicTensorLinearEquiv M N f s)) = basicTensorLinearEquiv M N f s
  change (affineTildeComparison M N).app (basicOpen f)
    (basicTensorLinearEquiv M N f s) = (unit M N).app (op (basicOpen f)) s at hc
  rw [hc]
  have hu := ConcreteCategory.congr_hom
    (NatTrans.congr_app (unit_tensorToTildeSheaf M N) (op (basicOpen f))) s
  rw [tensorToTilde_basic] at hu
  exact hu

/-- The canonical affine tilde comparison is invertible for quasi-coherent inputs. -/
instance affineTildeComparison_isIso : IsIso (affineTildeComparison M N) := by
  have : IsIso ((SheafOfModules.toSheaf _).map (affineTildeComparison M N)) :=
    ⟨⟨tensorToTildeSheaf M N, comparison_tensorToTildeSheaf M N,
      tensorToTildeSheaf_comparison M N⟩⟩
  have : IsIso ((Scheme.Modules.toPresheaf (Spec R)).map
      (affineTildeComparison M N)) :=
    inferInstanceAs (IsIso ((sheafToPresheaf _ _).map
      ((SheafOfModules.toSheaf _).map (affineTildeComparison M N))))
  exact isIso_of_reflects_iso _ (Scheme.Modules.toPresheaf (Spec R))

/-- Tilde of the actual global tensor is canonically the constructed sheaf tensor. -/
def affineTildeIso : tilde (affineTensorModule M N) ≅ tensor M N :=
  asIso (affineTildeComparison M N)

@[simp]
lemma affineTildeIso_hom : (affineTildeIso M N).hom = affineTildeComparison M N := rfl

end FLT.Mazur.FCurve.ModuleSheafTensor
