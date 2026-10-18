/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroDiagonalState
public import FLT.Mazur.WeierstrassDividedInitialPolygonLabels
public import FLT.Mazur.PolygonArithmeticParameterAnnihilator

/-!
# Actual diagonal parameters for the depth-zero revised polygon

The five cyclic nodes use their separate accumulated diagonal smoothings.
Their nilpotence follows from the proved annihilators over the original domain.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false

/-- Over the original domain, a top-power-annihilated arithmetic coefficient is nilpotent. -/
theorem arithmeticAnnihilatedCoefficient_nilpotent {R : Type} [CommRing R] [IsDomain R]
    {π : R} (hπ : π ≠ 0) (m : ℕ) (z : Quotient R π m)
    (hz : parameter R π m ^ m * z = 0) : IsNilpotent z := by
  cases m with
  | zero =>
    have he : z = 0 := by simpa only [pow_zero, one_mul] using hz
    exact he ▸ IsNilpotent.zero
  | succ m =>
    obtain ⟨w, rfl⟩ := (parameter_last_mul_eq_zero_iff R π hπ m z).mp hz
    exact ⟨m + 2, by rw [mul_pow, parameter_pow, zero_mul]⟩

variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (hj : 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "D" => arithmeticZeroDiagonalState hπ data H 0 hj u hu

/-- The actual common terminal, two last nodes and two initial nodes in cyclic order. -/
def arithmeticZeroDiagonalPolygonParameter (m : ℕ) : Fin 5 → Quotient R π m :=
  ![(D).terminal m, (D).last m false, (D).initial m false,
    (D).initial m true, (D).last m true]

local notation "p" => arithmeticZeroDiagonalPolygonParameter hπ data H hj u hu

/-- The terminal label uses every accumulated inverse terminal drift. -/
theorem arithmeticZeroDiagonalPolygonParameter_terminal (m : ℕ) :
    p m 0 = (D).terminal m := rfl

/-- Both original initial labels keep their actual separate diagonal parameters. -/
theorem arithmeticZeroDiagonalPolygonParameter_initial (m : ℕ) (b : Bool) :
    p m (initialPolygonIndex 1 b) = (D).initial m b := by cases b <;> rfl

/-- Each retained arm keeps the actual smoothing of its shared last node. -/
theorem arithmeticZeroDiagonalPolygonParameter_retained (m : ℕ) (a : Fin 1) (b : Bool) :
    p m (retainedPolygonIndex 1 a b) = (D).last m b := by
  have ha : a = 0 := Subsingleton.elim _ _
  subst a
  cases b <;> rfl

/-- All five diagonal smoothings are nilpotent without identifying them with a fixed parameter. -/
instance arithmeticZeroDiagonalPolygonParameter_nilpotent (m : ℕ) (i : Fin 5) :
    Fact (IsNilpotent (p m i)) := by
  constructor
  apply arithmeticAnnihilatedCoefficient_nilpotent hπ
  have h := arithmeticZeroDiagonalState_annihilated hπ data H 0 hj u hu
  fin_cases i
  · exact h.2.2 m
  · exact h.2.1 m false
  · exact h.1 m false
  · exact h.1 m true
  · exact h.2.1 m true

/-- Each separate diagonal node parameter follows the original arithmetic restriction. -/
theorem arithmeticZeroDiagonalPolygonParameter_restriction (m : ℕ) (i : Fin 5) :
    restriction R π m (p (m + 1) i) = p m i := by
  have h := arithmeticZeroDiagonalState_compatible hπ data H 0 hj u hu
  fin_cases i
  · exact h.2.2.1 m
  · exact h.2.1 m false
  · exact h.1 m false
  · exact h.1 m true
  · exact h.2.1 m true

end FLT.Mazur.WeierstrassDividedDepth
