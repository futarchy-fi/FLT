/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleLineBundleTensorPullback
public import FLT.Mazur.ModuleGlobalSectionPullback
/-!
# Tensor powers of actual module sections

Pure tensor powers restrict naturally and commute with the existing module
pullback and tensor-power comparison, including the unit in degree zero.
-/

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback
variable {X Y : Scheme.{u}}
/-- The pure tensor power of a section, with value one in degree zero. -/
def tensorPowerSection (M : X.Modules) (U : X.Opens) (s : Γ(M, U)) :
    (m : ℕ) → Γ(tensorPower M m, U)
  | 0 => (1 : Γ(X, U))
  | m + 1 => ModuleSheafTensor.pure M (tensorPower M m) U s (tensorPowerSection M U s m)
/-- Pure tensor powers commute with restriction to an open subset. -/
lemma tensorPowerSection_restrict (M : X.Modules) {U V : X.Opens}
    (h : U ≤ V) (s : Γ(M, V)) (m : ℕ) :
    (tensorPower M m).presheaf.map (homOfLE h).op (tensorPowerSection M V s m) =
      tensorPowerSection M U (M.presheaf.map (homOfLE h).op s) m := by
  induction m with
  | zero => exact map_one (X.presheaf.map (homOfLE h).op).hom
  | succ m ih =>
    change (ModuleSheafTensor.tensor M (tensorPower M m)).presheaf.map _
      (ModuleSheafTensor.pure _ _ _ _ _) = _
    rw [ModuleSheafTensor.pure_restrict, ih]
    rfl
/-- The existing tensor-power pullback comparison preserves powers of sections. -/
lemma tensorPowerSection_pullback (f : X ⟶ Y) (M : Y.Modules)
    (s : Γ(M, ⊤)) (m : ℕ) :
    (tensorPowerIso f M m).hom.app ⊤ (pullGlobal f _ (tensorPowerSection M ⊤ s m)) =
      tensorPowerSection ((pullback f).obj M) ⊤ (pullGlobal f M s) m := by
  induction m with
  | zero =>
    change (modulePullbackUnitIso f).hom.app ⊤
      (pullGlobal f (structureModule Y) (1 : Γ(Y, ⊤))) = (1 : Γ(X, ⊤))
    exact (modulePullbackUnitIso_unit f ⊤ 1).trans (map_one (f.app ⊤).hom)
  | succ m ih =>
    change (ModuleSheafTensor.map (𝟙 ((pullback f).obj M)) (tensorPowerIso f M m).hom).app ⊤
      ((tensorIso f M (tensorPower M m)).hom.app ⊤
        (pullGlobal f _ (ModuleSheafTensor.pure M (tensorPower M m) ⊤ s
          (tensorPowerSection M ⊤ s m)))) = _
    rw [show (tensorIso f M (tensorPower M m)).hom.app ⊤
      (pullGlobal f _ (ModuleSheafTensor.pure M (tensorPower M m) ⊤ s
        (tensorPowerSection M ⊤ s m))) =
      ModuleSheafTensor.pure _ _ ⊤ (pullGlobal f M s)
        (pullGlobal f _ (tensorPowerSection M ⊤ s m)) from
      tensorIso_adj_pure f M (tensorPower M m) ⊤ s (tensorPowerSection M ⊤ s m)]
    rw [ModuleSheafTensor.map_pure, ih]
    rfl
end FLT.Mazur.FCurve
