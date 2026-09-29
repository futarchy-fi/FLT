/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSheafTensorRestrict
public import FLT.Mazur.ProjectiveTwistingSheaf

/-!
# Twisting arbitrary module sheaves on projective space

The twist is the sheaf tensor with `O(d)`. Its coordinates on standard charts
are sections of the original sheaf, with transition `(Xⱼ/Xᵢ)^d`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite TensorProduct
open FLT.Mazur.FCurve

universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace FLT.Mazur.FCurve.ModuleSheafTensor

variable {X : Scheme.{u}}

/-- Tensoring a sheaf with the structure module needs no further sheafification. -/
lemma tensor_unit_isSheaf (M : X.Modules) :
    Presheaf.IsSheaf (Opens.grothendieckTopology X)
      (tensorPresheaf M (SheafOfModules.unit X.ringCatSheaf)).presheaf := by
  let e : tensorPresheaf M (SheafOfModules.unit X.ringCatSheaf) ≅ M.val :=
    MonoidalCategory.rightUnitor (show PresheafOfModulesOfCommRing X.presheaf from M.val)
  exact (Presheaf.isSheaf_of_iso_iff ((PresheafOfModules.toPresheaf _).mapIso e)).mpr
    M.isSheaf

/-- The structure module is a right unit for the constructed tensor. -/
def rightUnitor (M : X.Modules) :
    tensor M (SheafOfModules.unit X.ringCatSheaf) ≅ M := by
  let e : tensorPresheaf M (SheafOfModules.unit X.ringCatSheaf) ≅ M.val :=
    MonoidalCategory.rightUnitor (show PresheafOfModulesOfCommRing X.presheaf from M.val)
  let := isIso_unit_of_isSheaf M (SheafOfModules.unit X.ringCatSheaf)
    (tensor_unit_isSheaf M)
  exact (SheafOfModules.fullyFaithfulForget X.ringCatSheaf).preimageIso
    ((asIso (unit M (SheafOfModules.unit X.ringCatSheaf))).symm ≪≫ e)

/-- The right unit comparison evaluates a pure tensor by scalar multiplication. -/
@[simp]
lemma rightUnitor_pure (M : X.Modules) (U : X.Opens) (r : Γ(X, U)) (m : Γ(M, U)) :
    (rightUnitor M).hom.app U (pure M (SheafOfModules.unit X.ringCatSheaf) U m r) =
      r • m := by
  let := isIso_unit_of_isSheaf M (SheafOfModules.unit X.ringCatSheaf)
    (tensor_unit_isSheaf M)
  have h := congrArg (fun f ↦ f.app (.op U))
    (IsIso.hom_inv_id (unit M (SheafOfModules.unit X.ringCatSheaf)))
  have he := congrArg (fun f ↦ (ModuleCat.Hom.hom f) (m ⊗ₜ[Γ(X, U)] r)) h
  change (MonoidalCategory.rightUnitor
    (show PresheafOfModulesOfCommRing X.presheaf from M.val)).hom.app (.op U)
    ((inv (unit M (SheafOfModules.unit X.ringCatSheaf))).app (.op U)
      ((unit M (SheafOfModules.unit X.ringCatSheaf)).app (.op U) (m ⊗ₜ r))) = _
  rw [show (inv (unit M (SheafOfModules.unit X.ringCatSheaf))).app (.op U)
      ((unit M (SheafOfModules.unit X.ringCatSheaf)).app (.op U) (m ⊗ₜ r)) =
        m ⊗ₜ r from he]
  rfl

/-- Tensoring with a trivialized line sheaf leaves the other factor arbitrary. -/
def rightTrivialIso (M : X.Modules) {L : X.Modules}
    (e : L ≅ SheafOfModules.unit X.ringCatSheaf) : tensor M L ≅ M :=
  congr (Iso.refl M) e ≪≫ rightUnitor M

/-- The coefficient of a pure tensor is the line coefficient times the section. -/
@[simp]
lemma rightTrivialIso_pure (M : X.Modules) {L : X.Modules}
    (e : L ≅ SheafOfModules.unit X.ringCatSheaf)
    (U : X.Opens) (m : Γ(M, U)) (l : Γ(L, U)) :
    (rightTrivialIso M e).hom.app U (pure M L U m l) =
      (show Γ(X, U) from e.hom.app U l) • m := by
  change (rightUnitor M).hom.app U ((map (𝟙 M) e.hom).app U _) = _
  rw [map_pure, rightUnitor_pure]
  rfl

/-- Inverse coordinates tensor a section with the chosen local basis. -/
lemma rightTrivialIso_inv (M : X.Modules) {L : X.Modules}
    (e : L ≅ SheafOfModules.unit X.ringCatSheaf) (U : X.Opens) (m : Γ(M, U)) :
    (rightTrivialIso M e).inv.app U m = pure M L U m (e.inv.app U (1 : Γ(X, U))) := by
  apply (sectionsCongr (rightTrivialIso M e) U).injective
  change (sectionsCongr (rightTrivialIso M e) U)
    ((sectionsCongr (rightTrivialIso M e) U).symm m) = _
  rw [LinearEquiv.apply_symm_apply, sectionsCongr_apply, rightTrivialIso_pure]
  have he : e.hom.app U (e.inv.app U (1 : Γ(X, U))) = (1 : Γ(X, U)) :=
    (sectionsCongr e U).apply_symm_apply (1 : Γ(X, U))
  rw [he, one_smul]

end FLT.Mazur.FCurve.ModuleSheafTensor

namespace FLT.Mazur.ProjectiveSpace

open ModuleSheafTensor

variable (R : Type u) [CommRing R] (ι : Type u)

/-- The integer twist of an arbitrary module sheaf on polynomial projective space. -/
def twistTensor (F : (space R ι).Modules) (d : ℤ) : (space R ι).Modules :=
  tensor F (twistingSheaf R ι d)

/-- Coordinates on every subopen of a standard chart, with values in `F`. -/
def twistTensorOnOpenIso (F : (space R ι).Modules) (d : ℤ) (i : ι)
    (V : (space R ι).Opens) (hi : V ≤ chart R ι i) :
    (twistTensor R ι F d).restrict V.ι ≅ F.restrict V.ι :=
  ModuleSheafTensor.restrictIso F (twistingSheaf R ι d) V.ι ≪≫
    rightTrivialIso (F.restrict V.ι) ((twistCocycle R ι d).onOpenIso i V hi)

/-- The standard-chart trivialization of the twist of `F`. -/
def twistTensorRestrictIso (F : (space R ι).Modules) (d : ℤ) (i : ι) :
    (twistTensor R ι F d).restrict (chart R ι i).ι ≅ F.restrict (chart R ι i).ι :=
  twistTensorOnOpenIso R ι F d i (chart R ι i) le_rfl

/-- Coordinates of a pure tensor on a subopen of a standard chart. -/
lemma twistTensorOnOpenIso_pure (F : (space R ι).Modules) (d : ℤ) (i : ι)
    (V : (space R ι).Opens) (hi : V ≤ chart R ι i) (W : V.toScheme.Opens)
    (m : Γ(F, V.ι ''ᵁ W)) (l : Γ(twistingSheaf R ι d, V.ι ''ᵁ W)) :
    (twistTensorOnOpenIso R ι F d i V hi).hom.app W
      (((twistTensor R ι F d).restrictAppIso V.ι W).inv
        (pure F (twistingSheaf R ι d) (V.ι ''ᵁ W) m l)) =
    (show Γ(V.toScheme, W) from
      ((twistCocycle R ι d).onOpenIso i V hi).hom.app W
        (((twistingSheaf R ι d).restrictAppIso V.ι W).inv l)) •
      (F.restrictAppIso V.ι W).inv m := by
  exact (congrArg
    ((rightTrivialIso (F.restrict V.ι)
      ((twistCocycle R ι d).onOpenIso i V hi)).hom.app W)
    (restrictIso_hom_pure F (twistingSheaf R ι d) V.ι W m l)).trans
      (rightTrivialIso_pure (F.restrict V.ι)
        ((twistCocycle R ι d).onOpenIso i V hi) W
        ((F.restrictAppIso V.ι W).inv m)
        (((twistingSheaf R ι d).restrictAppIso V.ι W).inv l))

/-- Inverse chart coordinates are pure tensors with the chart basis of `O(d)`. -/
lemma twistTensorOnOpenIso_inv (F : (space R ι).Modules) (d : ℤ) (i : ι)
    (V : (space R ι).Opens) (hi : V ≤ chart R ι i) (W : V.toScheme.Opens)
    (m : Γ(F.restrict V.ι, W)) :
    (twistTensorOnOpenIso R ι F d i V hi).inv.app W m =
      ((twistTensor R ι F d).restrictAppIso V.ι W).inv
        (pure F (twistingSheaf R ι d) (V.ι ''ᵁ W)
          ((F.restrictAppIso V.ι W).hom m)
          (((twistingSheaf R ι d).restrictAppIso V.ι W).hom
            (((twistCocycle R ι d).onOpenIso i V hi).inv.app W (1 : Γ(V.toScheme, W))))) := by
  change (restrictComparison F (twistingSheaf R ι d) V.ι).app W
    ((rightTrivialIso _ _).inv.app W m) = _
  rw [rightTrivialIso_inv]
  exact restrictComparison_pure F (twistingSheaf R ι d) V.ι W m _

/-- Changing coordinates multiplies any local `F`-section by `(Xⱼ/Xᵢ)^d`. -/
theorem twistTensor_change (F : (space R ι).Modules) (d : ℤ) (i j : ι)
    (V : (space R ι).Opens) (hi : V ≤ chart R ι i) (hj : V ≤ chart R ι j)
    (W : V.toScheme.Opens) (m : Γ(F.restrict V.ι, W)) :
    ((twistTensorOnOpenIso R ι F d j V hj).inv ≫
      (twistTensorOnOpenIso R ι F d i V hi).hom).app W m =
    (show Γ(V.toScheme, W) from
      ((restrictUnits R ι (le_inf ((V.ι_image_le W).trans hi)
        ((V.ι_image_le W).trans hj)) (twistTransition R ι 1 i j) ^ d :
          Γ(space R ι, V.ι ''ᵁ W)ˣ) : Γ(space R ι, V.ι ''ᵁ W))) • m := by
  change (twistTensorOnOpenIso R ι F d i V hi).hom.app W
    ((twistTensorOnOpenIso R ι F d j V hj).inv.app W m) = _
  rw [twistTensorOnOpenIso_inv, twistTensorOnOpenIso_pure]
  have h := twistingSheaf_change R ι d i j V hi hj W 1
  simp only [mul_one] at h
  change ((twistCocycle R ι d).onOpenIso i V hi).hom.app W
    (((twistCocycle R ι d).onOpenIso j V hj).inv.app W (1 : Γ(V.toScheme, W))) = _ at h
  change (show Γ(V.toScheme, W) from
    ((twistCocycle R ι d).onOpenIso i V hi).hom.app W
      (((twistCocycle R ι d).onOpenIso j V hj).inv.app W (1 : Γ(V.toScheme, W)))) • m = _
  rw [h]

/-- Coordinates of every twisted section satisfy the coordinate transition equation. -/
theorem twistTensor_transition (F : (space R ι).Modules) (d : ℤ) (i j : ι)
    (V : (space R ι).Opens) (hi : V ≤ chart R ι i) (hj : V ≤ chart R ι j)
    (W : V.toScheme.Opens) (s : Γ((twistTensor R ι F d).restrict V.ι, W)) :
    (twistTensorOnOpenIso R ι F d i V hi).hom.app W s =
    (show Γ(V.toScheme, W) from
      ((restrictUnits R ι (le_inf ((V.ι_image_le W).trans hi)
        ((V.ι_image_le W).trans hj)) (twistTransition R ι 1 i j) ^ d :
          Γ(space R ι, V.ι ''ᵁ W)ˣ) : Γ(space R ι, V.ι ''ᵁ W))) •
      (twistTensorOnOpenIso R ι F d j V hj).hom.app W s := by
  have h := twistTensor_change R ι F d i j V hi hj W
    ((twistTensorOnOpenIso R ι F d j V hj).hom.app W s)
  have he : (twistTensorOnOpenIso R ι F d j V hj).inv.app W
      ((twistTensorOnOpenIso R ι F d j V hj).hom.app W s) = s :=
    (sectionsCongr (twistTensorOnOpenIso R ι F d j V hj) W).symm_apply_apply s
  change (twistTensorOnOpenIso R ι F d i V hi).hom.app W
    ((twistTensorOnOpenIso R ι F d j V hj).inv.app W
      ((twistTensorOnOpenIso R ι F d j V hj).hom.app W s)) = _ at h
  rwa [he] at h

end FLT.Mazur.ProjectiveSpace
