/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LineSectionTwistSystem
public import FLT.Mazur.TensorPowerGeneratorOpen

/-!
# Coordinates of the actual section-twist transitions

A trivialization identifies each coefficient twist with the coefficient
module. The transition from stage n to stage n+d is multiplication by the
d-th power of the coordinate of the given line section.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open Scheme.Modules

universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FLT.Mazur.FCurve.LineSectionTwistSystem

open ModuleSheafTensor ModuleLineBundleTensorPullback

variable {X : Scheme.{u}} (M : X.Modules) {L : X.Modules}
  (e : L ≅ structureModule X)

/-- Coordinates for every term of the actual section-twist system. -/
def coordinates (n : ℕ) : tensor M (tensorPower L n) ≅ M :=
  rightTrivialIso M (tensorPowerTrivialization e n)

/-- The coordinates of a pure coefficient tensor. -/
lemma coordinates_pure (n : ℕ) (U : X.Opens) (m : Γ(M, U))
    (t : Γ(tensorPower L n, U)) :
    (coordinates M e n).hom.app U (pure M (tensorPower L n) U m t) =
      (show Γ(X, U) from (tensorPowerTrivialization e n).hom.app U t) • m :=
  rightTrivialIso_pure M (tensorPowerTrivialization e n) U m t

/-- Inserting the section in a line power multiplies its scalar coordinate. -/
lemma powerStep_coordinates (s : Γ(L, ⊤)) (n : ℕ) (U : X.Opens)
    (t : Γ(tensorPower L n, U)) :
    (tensorPowerTrivialization e (n + 1)).hom.app U ((powerStep s n).app U t) =
      X.presheaf.map U.leTop.op (e.hom.app ⊤ s) *
        (show Γ(X, U) from (tensorPowerTrivialization e n).hom.app U t) := by
  rw [powerStep_app]
  change (trivialTensorIso e (tensorPowerTrivialization e n)).hom.app U
    (pure L (tensorPower L n) U _ t) = _
  rw [trivialTensorIso_pure]
  congr 1
  exact ConcreteCategory.congr_hom (e.hom.val.naturality U.leTop.op) s

/-- The successor formula on arbitrary sections, not only pure tensors. -/
lemma step_coordinates (s : Γ(L, ⊤)) (n : ℕ) (U : X.Opens)
    (t : Γ(tensor M (tensorPower L n), U)) :
    (coordinates M e (n + 1)).hom.app U ((step M s n).app U t) =
      X.presheaf.map U.leTop.op (e.hom.app ⊤ s) • (coordinates M e n).hom.app U t := by
  obtain ⟨m, hm⟩ := (ConcreteCategory.bijective_of_isIso
    ((coordinates M e n).inv.app U)).surjective t
  rw [← hm]
  have hc : (coordinates M e n).hom.app U ((coordinates M e n).inv.app U m) = m :=
    (sectionsCongr (coordinates M e n) U).apply_symm_apply m
  rw [hc]
  change (coordinates M e (n + 1)).hom.app U ((step M s n).app U
    ((rightTrivialIso M (tensorPowerTrivialization e n)).inv.app U m)) = _
  rw [rightTrivialIso_inv, step_pure, coordinates_pure]
  change (show Γ(X, U) from (trivialTensorIso e (tensorPowerTrivialization e n)).hom.app U
    (pure L (tensorPower L n) U _ _)) • m = _
  rw [trivialTensorIso_pure]
  have he : e.hom.app U (L.presheaf.map U.leTop.op s) =
      X.presheaf.map U.leTop.op (e.hom.app ⊤ s) :=
    ConcreteCategory.congr_hom (e.hom.val.naturality U.leTop.op) s
  have ht : (tensorPowerTrivialization e n).hom.app U
      ((tensorPowerTrivialization e n).inv.app U (1 : Γ(X, U))) = (1 : Γ(X, U)) :=
    (sectionsCongr (tensorPowerTrivialization e n) U).apply_symm_apply (1 : Γ(X, U))
  erw [he, ht, mul_one]

/-- Every actual transition is multiplication by a scalar power in these coordinates. -/
theorem map_coordinates (s : Γ(L, ⊤)) (n d : ℕ) (U : X.Opens)
    (t : Γ((system M s).obj n, U)) :
    (coordinates M e (n + d)).hom.app U
        (((system M s).map (homOfLE (Nat.le_add_right n d))).app U t) =
      (X.presheaf.map U.leTop.op (e.hom.app ⊤ s)) ^ d •
        (coordinates M e n).hom.app U t := by
  induction d with
  | zero => simp
  | succ d ih =>
    have he : homOfLE (Nat.le_add_right n (d + 1)) =
        homOfLE (Nat.le_add_right n d) ≫ homOfLE (Nat.le_add_right (n + d) 1) := rfl
    rw [he, Functor.map_comp, system_map_succ]
    change (coordinates M e (n + d + 1)).hom.app U
      ((step M s (n + d)).app U
        (((system M s).map (homOfLE (Nat.le_add_right n d))).app U t)) = _
    rw [step_coordinates, ih, pow_succ', mul_smul]

end FLT.Mazur.FCurve.LineSectionTwistSystem
