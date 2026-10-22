/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleTensorFramePullback
public import FLT.Mazur.TensorPowerPullbackComparison

/-!
# Pullback and transport of tensor-power frames

All degrees of a frame transport together. The comparison is an equality
of sheaf morphisms, so it applies to arbitrary sections and nilpotent bases.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] ModuleSheafTensor.tensor Scheme.Modules.pullback tensorIso
variable {X Y : Scheme}

/-- Tensor-power frames preserve an actual isomorphism of the original lines. -/
theorem tensorPowerTrivialization_transport {L M : X.Modules}
    (e : L ≅ M) (v : M ≅ structureModule X) (n : ℕ) :
    (tensorPowerCongr e n).hom ≫ (tensorPowerTrivialization v n).hom =
      (tensorPowerTrivialization (e ≪≫ v) n).hom := by
  induction n with
  | zero => simp [tensorPowerCongr, tensorPowerTrivialization]
  | succ n ih =>
    simp only [tensorPowerCongr, tensorPowerTrivialization,
      ModuleSheafTensor.trivialTensorIso, ModuleSheafTensor.congr, Iso.trans_hom]
    rw [← Category.assoc, ← ModuleSheafTensor.map_comp, ih]

/-- Every tensor-power frame commutes with arbitrary sheaf pullback. -/
theorem tensorPowerTrivialization_pullback (f : X ⟶ Y) {L : Y.Modules}
    (e : L ≅ structureModule Y) (n : ℕ) :
    (tensorPowerIso f L n).hom ≫
      (tensorPowerTrivialization (pulledGlobalFrame f e) n).hom =
        (pulledGlobalFrame f (tensorPowerTrivialization e n)).hom := by
  induction n with
  | zero =>
    simp only [tensorPowerIso_zero, tensorPowerTrivialization, Iso.refl_hom,
      Category.comp_id, pulledGlobalFrame, Iso.trans_hom, Functor.mapIso_hom]
    change _ = (pullback f).map (𝟙 (structureModule Y)) ≫ _
    erw [CategoryTheory.Functor.map_id, Category.id_comp]
  | succ n ih =>
    simp only [tensorPowerIso_succ, tensorPowerTrivialization,
      ModuleSheafTensor.trivialTensorIso, ModuleSheafTensor.congr, Iso.trans_hom,
      Iso.refl_hom, Category.assoc]
    rw [← Category.assoc (ModuleSheafTensor.map _ _),
      ← ModuleSheafTensor.map_comp, Category.id_comp, ih]
    exact pulledGlobalFrame_tensor f e (tensorPowerTrivialization e n)

end FLT.Mazur.FCurve
