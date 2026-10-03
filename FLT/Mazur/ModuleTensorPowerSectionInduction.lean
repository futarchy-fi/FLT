/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSectionMap
/-!
# Section preservation for recursive tensor comparisons

Carry out the tensor-power induction with abstract module sheaves. Concrete
geometric comparisons need only supply their unit and multiplication laws.
-/

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback
variable {X : Scheme.{u}}
/-- A recursive family of tensor comparisons preserves recursively compatible sections. -/
lemma sectionPower_induction (M : X.Modules) (N : ℕ → X.Modules)
    (e : ∀ m, tensorPower M m ≅ N m) (z : structureModule X ≅ N 0)
    (f : ∀ m, ModuleSheafTensor.tensor M (N m) ≅ N (m + 1))
    (hz : e 0 = z) (hf : ∀ m, e (m + 1) = ModuleSheafTensor.congr (Iso.refl M) (e m) ≪≫ f m)
    (U : X.Opens) (s : Γ(M, U)) (t : ∀ m, Γ(N m, U))
    (hzs : z.hom.app U (1 : Γ(X, U)) = t 0)
    (hfs : ∀ m, (f m).hom.app U (ModuleSheafTensor.pure M (N m) U s (t m)) = t (m + 1))
    (m : ℕ) : (e m).hom.app U (tensorPowerSection M U s m) = t m := by
  induction m with
  | zero => rw [hz]; exact hzs
  | succ m ih =>
    rw [hf]
    change (ModuleSheafTensor.congr (Iso.refl M) (e m) ≪≫ f m).hom.app U
      (ModuleSheafTensor.pure M (tensorPower M m) U s (tensorPowerSection M U s m)) = _
    rw [sectionIso_trans, sectionTensor_congr]
    simpa only [Iso.refl_hom, Hom.id_app, AddCommGrpCat.id_apply, ih] using hfs m
end FLT.Mazur.FCurve
