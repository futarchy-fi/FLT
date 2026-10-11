/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionGradedCoordinates
public import FLT.Mazur.SectionGradedPullback
public import FLT.Mazur.ClosedPointLineSection

/-!
# Nonzero products in trivialized line fibers

Over a ring without zero divisors, nonzero sections in tensor powers of a
trivialized line have nonzero graded product. The coordinates are the actual
tensor-power trivializations, so the statement applies to restricted line fibers.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.SectionGradedCoordinates
open FCurve ModuleLineBundleTensorPullback SectionGradedMultiplication
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {X : Scheme.{u}} {L : X.Modules} (e : L ≅ structureModule X)

/-- Tensor-power coordinates detect zero sections. -/
theorem coordinate_eq_zero_iff (n : ℕ) (U : X.Opens) (s : Piece L U n) :
    coordinate e n U s = 0 ↔ s = 0 := by
  constructor
  · intro hs
    apply (ConcreteCategory.bijective_of_isIso
      ((tensorPowerTrivialization e n).hom.app U)).injective
    exact hs.trans (map_zero _).symm
  · rintro rfl
    exact map_zero _

include e in
/-- Nonzero tensor-power sections multiply nontrivially over a domain of coordinates. -/
theorem mul_ne_zero (U : X.Opens) [NoZeroDivisors Γ(X, U)]
    (m n : ℕ) (s : Piece L U m) (t : Piece L U n) (hs : s ≠ 0) (ht : t ≠ 0) :
    SectionGradedMultiplication.mul L U m n s t ≠ 0 := by
  apply (coordinate_eq_zero_iff e (m + n) U _).not.mp
  rw [coordinate_mul]
  exact _root_.mul_ne_zero ((coordinate_eq_zero_iff e m U s).not.mpr hs)
    ((coordinate_eq_zero_iff e n U t).not.mpr ht)

/-- The tensor-power comparison preserves whether a pulled-back section vanishes. -/
theorem pull_eq_zero_iff {Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules) (n : ℕ)
    (s : Piece M ⊤ n) :
    SectionGradedPullback.pull f M n ⊤ s = 0 ↔ pullGlobal f (tensorPower M n) s = 0 := by
  change (tensorPowerIso f M n).hom.app ⊤ (pullGlobal f (tensorPower M n) s) = 0 ↔ _
  constructor
  · intro hs
    apply (ConcreteCategory.bijective_of_isIso ((tensorPowerIso f M n).hom.app ⊤)).injective
    exact hs.trans (map_zero _).symm
  · intro hs
    rw [hs, map_zero]

/-- On an integral one-point scheme, nonzero restrictions of line sections multiply nontrivially. -/
theorem pullGlobal_mul_ne_zero {Y : Scheme} {Z : Scheme} (f : Z ⟶ Y)
    [IsIntegral Z] [Subsingleton Z] {M : Y.Modules} (hM : LocallyFreeRankOne M)
    (m n : ℕ) (s : Piece M ⊤ m) (t : Piece M ⊤ n)
    (hs : pullGlobal f (tensorPower M m) s ≠ 0)
    (ht : pullGlobal f (tensorPower M n) t ≠ 0) :
    pullGlobal f (tensorPower M (m + n))
      (SectionGradedMultiplication.mul M ⊤ m n s t) ≠ 0 := by
  obtain ⟨e⟩ := (hM.pullback f).trivial_of_subsingleton (Classical.ofNonempty : Z)
  apply (pull_eq_zero_iff f M (m + n) _).not.mp
  rw [SectionGradedPullback.pull_mul]
  exact mul_ne_zero e ⊤ m n _ _ ((pull_eq_zero_iff f M m s).not.mpr hs)
    ((pull_eq_zero_iff f M n t).not.mpr ht)

end FLT.Mazur.SectionGradedCoordinates
