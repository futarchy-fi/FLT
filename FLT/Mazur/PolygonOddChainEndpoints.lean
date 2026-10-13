/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.CyclicPinchingReflection

/-!
# Cyclic endpoint equations from two complete projective chains

An exterior and two equally long chains form an odd cycle when consecutive
components meet, their last infinities agree, and their first zeros attach to
the ordered exterior. The first chain uses its entire reversed parameter.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.PolygonPinching
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable (K : Type u) [Field K] {X : Scheme.{u}} (n m : ℕ) (hn : n = 2 * m + 3)
  (F : ProjectiveLine.scheme K ⟶ X)
  (B : Fin (m + 1) → Fin 2 → (ProjectiveLine.scheme K ⟶ X))
  (C : Fin n → (ProjectiveLine.scheme K ⟶ X))
local notation "ρ" => ProjectiveLine.endpointReversal K

/-- Original full component formulas and chain attachments give every cyclic endpoint. -/
theorem oddChain_endpoints
    (hzero : C ⟨0, by omega⟩ = F)
    (hfirst : ∀ j : Fin (m + 1), C ⟨j.val + 1, by omega⟩ = ρ ≫ B j 0)
    (hsecond : ∀ j : Fin (m + 1), C ⟨n - 1 - j.val, by omega⟩ = B j 1)
    (hleft : ProjectiveLine.zero K ≫ F = ProjectiveLine.zero K ≫ B 0 0)
    (hright : ProjectiveLine.zero K ≫ B 0 1 = ProjectiveLine.infinity K ≫ F)
    (hjoin : ∀ (j : Fin m) (b : Fin 2), ProjectiveLine.infinity K ≫ B j.castSucc b =
      ProjectiveLine.zero K ≫ B j.succ b)
    (hfinal : ProjectiveLine.infinity K ≫ B (Fin.last m) 0 =
      ProjectiveLine.infinity K ≫ B (Fin.last m) 1)
    (i : Fin n) : ProjectiveLine.zero K ≫ C i =
      ProjectiveLine.infinity K ≫ C (next (by omega) i) := by
  subst n
  have hnext (hi : i.val + 1 < 2 * m + 3) :
      next (by omega) i = (⟨i.val + 1, hi⟩ : Fin (2 * m + 3)) := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt hi
  by_cases hz : i.val = 0
  · have hi : i = (0 : Fin (2 * m + 3)) := Fin.ext hz
    subst i
    rw [hnext (by omega)]
    change ProjectiveLine.zero K ≫ C ⟨0, by omega⟩ =
      ProjectiveLine.infinity K ≫ C ⟨(0 : Fin (m + 1)).val + 1, by omega⟩
    rw [hzero, hfirst, ProjectiveLine.infinity_endpointReversal_assoc]
    exact hleft
  by_cases hf : i.val ≤ m
  · let j : Fin m := ⟨i.val - 1, by omega⟩
    have hi : i = ⟨j.castSucc.val + 1, by omega⟩ := Fin.ext (by dsimp [j]; omega)
    have hs : (⟨i.val + 1, by omega⟩ : Fin (2 * m + 3)) =
        ⟨j.succ.val + 1, by omega⟩ := Fin.ext (by dsimp [j]; omega)
    rw [hnext (by omega), hs]
    conv_lhs => rw [hi]
    rw [hfirst, hfirst, ProjectiveLine.zero_endpointReversal_assoc,
      ProjectiveLine.infinity_endpointReversal_assoc]
    exact hjoin j 0
  by_cases ht : i.val = m + 1
  · have hi : i = ⟨(Fin.last m).val + 1, by omega⟩ := Fin.ext ht
    have hs : (⟨i.val + 1, by omega⟩ : Fin (2 * m + 3)) =
        ⟨2 * m + 3 - 1 - (Fin.last m).val, by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hnext (by omega), hs]
    conv_lhs => rw [hi]
    rw [hfirst, hsecond, ProjectiveLine.zero_endpointReversal_assoc]
    exact hfinal
  by_cases hl : i.val = 2 * m + 2
  · have hi : i = ⟨2 * m + 3 - 1 - (0 : Fin (m + 1)).val, by omega⟩ :=
      Fin.ext (by dsimp; omega)
    have hs : next (by omega) i = (⟨0, by omega⟩ : Fin (2 * m + 3)) := by
      apply Fin.ext
      change (i.val + 1) % (2 * m + 3) = 0
      rw [show i.val + 1 = 2 * m + 3 by omega, Nat.mod_self]
    rw [hs]
    conv_lhs => rw [hi]
    rw [hsecond, hzero]
    exact hright
  · let j : Fin m := ⟨2 * m + 1 - i.val, by omega⟩
    have hi : i = ⟨2 * m + 3 - 1 - j.succ.val, by omega⟩ :=
      Fin.ext (by dsimp [j]; omega)
    have hs : (⟨i.val + 1, by omega⟩ : Fin (2 * m + 3)) =
        ⟨2 * m + 3 - 1 - j.castSucc.val, by omega⟩ := Fin.ext (by dsimp [j]; omega)
    rw [hnext (by omega), hs]
    conv_lhs => rw [hi]
    rw [hsecond, hsecond]
    exact (hjoin j 1).symm

end FLT.Mazur.PolygonPinching
