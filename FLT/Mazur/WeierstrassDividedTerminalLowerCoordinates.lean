/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedRetainedOlderCoordinates

/-!
# Terminal coordinates at every depth up to the final stage

The terminal input may keep its own depth, including stage zero, or contract
only to a chosen intermediate depth. The full integral chart is the source.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
variable {R : Type*} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (j : ℕ) (hj : j ≤ n) (k : ℕ) (hk : k ≤ j)
local notation "d" => data ⟨k, Nat.lt_succ_of_le (hk.trans hj)⟩
local notation "e" => data ⟨j, Nat.lt_succ_of_le hj⟩

/-- The terminal divided chart contracts to any selected earlier divided depth. -/
def terminalLowerCoordinates :
    globalIntegralAtlasObject data j hj (1 : Fin (j + 3)) ⟶ chart d :=
  depthTransitionMorphism π (start + k) (start + j) hπ (Nat.add_le_add_left hk start) W
    (d).b3 (d).b4 (d).b6 (e).b3 (e).b4 (e).b6
    (d).factor3 (d).factor4 (d).factor6 (e).factor3 (e).factor4 (e).factor6

omit [IsBezout R] in
/-- The own-depth terminal map is the identity, with no positive-depth assumption. -/
theorem terminalLowerCoordinates_self :
    terminalLowerCoordinates hπ data j hj j le_rfl = 𝟙 (chart e) := by
  unfold terminalLowerCoordinates depthTransitionMorphism
  rw [depthTransition_self]
  exact Spec.map_id _

/-- Lower terminal coordinates retain the full original cubic input. -/
@[reassoc] theorem terminalLowerCoordinates_cubic :
    terminalLowerCoordinates hπ data j hj k hk ≫ toCurve d =
      globalIntegralAtlasMap hπ data j hj (1 : Fin (j + 3)) ≫
        finiteGlobalContraction hπ data j hj := by
  change terminalLowerCoordinates hπ data j hj k hk ≫ toCurve d =
    finiteSecantDividedChart hπ data j hj ≫ finiteGlobalContraction hπ data j hj
  rw [finiteSecantDividedChart_contraction]
  exact depthTransitionMorphism_contraction π (start + k) (start + j) hπ
    (Nat.add_le_add_left hk start) W (d).b3 (d).b4 (d).b6 (e).b3 (e).b4 (e).b6
    (d).factor3 (d).factor4 (d).factor6 (e).factor3 (e).factor4 (e).factor6

/-- The terminal coordinate map preserves the actual coefficient morphism. -/
@[reassoc] theorem terminalLowerCoordinates_structure :
    terminalLowerCoordinates hπ data j hj k hk ≫
        Spec.map (CommRingCat.ofHom (algebraMap R
          (Coordinate W (π ^ (start + k)) (d).b3 (d).b4 (d).b6))) =
      globalIntegralAtlasMap hπ data j hj (1 : Fin (j + 3)) ≫
        finiteGlobalStructure hπ data j hj := by
  rw [← toCurve_structure d, ← Category.assoc, terminalLowerCoordinates_cubic,
    Category.assoc]
  rw [finiteGlobalStructure]

end FLT.Mazur.WeierstrassDividedDepth
