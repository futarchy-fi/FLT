/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticPositiveRetainedCompatibility

/-!
# All positive-retention initial and terminal boundary compatibility

The two first and two last standard puncture equations imply compatibility
with every retained label. Index transports retain the exact original chart maps.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
local notation "c" => arithmeticLabeledAtlasMap hπ data H m (j + 1) hj
variable {Y : Scheme.{0}}
  (f : ∀ i, arithmeticLabeledAtlasObject hπ data H m (j + 1) hj i ⟶ Y)
local notation "C" => fun (i k : ArithmeticChartLabel (j + 1)) =>
  pullback.fst (c i) (c k) ≫ f i = pullback.snd (c i) (c k) ≫ f k

/-- The first two standard puncture equations control every initial/retained ordered pair. -/
theorem arithmeticPositive_initial_retained_compatible
    (hI : arithmeticPositiveInitialCompatible hπ data H m j hj f)
    (a : Fin (j + 1)) (u v : Bool) : C (.initial u) (.retained a v) := by
  by_cases ha : a.val = 0
  · have he : a = ⟨0, Nat.zero_lt_succ j⟩ := Fin.ext ha
    rw [he]
    by_cases huv : u = v
    · subst v
      exact (arithmeticPositiveInitial_compatible_iff hπ data H m j hj f).mp hI u
    · exact arithmeticEmptyPullback_compatible
        (arithmeticLabeledAtlas_initial_crossLabel_isPullback
          hπ data H m (j + 1) hj (Nat.zero_lt_succ j) u v huv) _ _
  · exact TernaryOpenDescent.disjoint_compatible _ _ _ _
      (arithmeticLabeledAtlas_initial_nonadjacent_disjoint
        hπ data m H (j + 1) hj a (by omega) u v)

/-- Both full terminal standard punctures control every terminal/retained ordered pair. -/
theorem arithmeticPositive_terminal_retained_compatible
    (hT : arithmeticPositiveTerminalCompatible hπ data H m j hj f)
    (a : Fin (j + 1)) (b : Bool) : C .terminal (.retained a b) := by
  by_cases ha : a.val = j
  · have he : a = ⟨j, by omega⟩ := Fin.ext ha
    rw [he]
    exact (arithmeticPositiveTerminal_compatible_iff hπ data H m j hj f).mp hT b
  · exact TernaryOpenDescent.disjoint_compatible _ _ _ _
      (arithmeticLabeledAtlas_earlier_terminal_disjoint
        hπ data H m (j + 1) hj a (by omega) b).symm

end FLT.Mazur.WeierstrassDividedDepth
