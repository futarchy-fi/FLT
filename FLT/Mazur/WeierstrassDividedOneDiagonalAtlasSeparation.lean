/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOneDiagonalInitialIntersection
public import FLT.Mazur.WeierstrassDividedArithmeticLabeledSeparation
public import FLT.Mazur.WeierstrassDividedArithmeticLabeledEarlierTerminal
public import FLT.Mazur.WeierstrassDividedZeroDiagonalAtlasSeparation

/-!
# Empty intersections of the complete corrected depth-one atlas

Transport the original full-chart exclusions through the actual finite chart
and global isomorphisms. No boundary coefficient reduction is involved.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticOneFiniteAtlasIso simultaneousTwistedArithmeticIso

variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 2 ≤ n)
  (u : Rˣ) (hu : (data ⟨2, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "c" => arithmeticOneDiagonalAtlasChart hπ data H m hj u hu
local notation "E" => arithmeticOneFiniteAtlasIso hπ data H m m hj u hu
local notation "G" => simultaneousTwistedArithmeticIso hπ data H m 1 hj u hu

/-- All original disjoint labeled chart pairs remain disjoint in the full diagonal atlas. -/
theorem arithmeticOneDiagonalAtlas_disjoint_of_original (i j : ArithmeticChartLabel 2)
    (h : Disjoint (Set.range (arithmeticLabeledAtlasMap hπ data H m 2 hj i))
      (Set.range (arithmeticLabeledAtlasMap hπ data H m 2 hj j))) :
    Disjoint (Set.range (c i)) (Set.range (c j)) :=
  fullChartIso_disjoint (E i) (E j) G
    (arithmeticOneFiniteAtlasIso_chart hπ data H m m hj u hu i).symm
    (arithmeticOneFiniteAtlasIso_chart hπ data H m m hj u hu j).symm h

/-- Neither full corrected first retained node meets the original infinity chart. -/
theorem arithmeticOneDiagonalAtlas_retained_infinity_disjoint (b : Bool) :
    Disjoint (Set.range (c (.retained ⟨0, by omega⟩ b))) (Set.range (c .infinity)) :=
  arithmeticOneDiagonalAtlas_disjoint_of_original hπ data H m hj u hu _ _
    (arithmeticLabeledAtlas_retained_infinity_disjoint hπ data H m 2 hj ⟨0, by omega⟩ b
      (by omega))

/-- An initial chart misses the full retained node of the opposite label. -/
theorem arithmeticOneDiagonalAtlas_initial_crossLabel_disjoint
    (b d : Bool) (hbd : b ≠ d) :
    Disjoint (Set.range (c (.initial b))) (Set.range (c (.retained ⟨0, by omega⟩ d))) :=
  arithmeticOneDiagonalAtlas_disjoint_of_original hπ data H m hj u hu _ _
    (emptyPullback_disjoint_ranges
      (arithmeticLabeledAtlas_initial_crossLabel_isPullback hπ data H m 2 hj (by omega) b d hbd))

/-- The two complete first retained nodes remain disjoint after every finite correction. -/
theorem arithmeticOneDiagonalAtlas_retained_disjoint :
    Disjoint (Set.range (c (.retained ⟨0, by omega⟩ false)))
      (Set.range (c (.retained ⟨0, by omega⟩ true))) :=
  arithmeticOneDiagonalAtlas_disjoint_of_original hπ data H m hj u hu _ _
    (emptyPullback_disjoint_ranges
      (arithmeticLabeledAtlas_sameDepth_isPullback hπ data H m 2 hj ⟨0, by omega⟩
        false true Bool.false_ne_true))

/-- The complete terminal remains disjoint from the full infinity chart. -/
theorem arithmeticOneDiagonalAtlas_terminal_infinity_disjoint :
    Disjoint (Set.range (c .terminal)) (Set.range (c .infinity)) :=
  arithmeticOneDiagonalAtlas_disjoint_of_original hπ data H m hj u hu _ _
    (arithmeticLabeledAtlas_terminal_infinity_disjoint hπ data H m 2 hj (by omega))

/-- Neither complete original initial open meets the common terminal. -/
theorem arithmeticOneDiagonalAtlas_initial_terminal_disjoint (b : Bool) :
    Disjoint (Set.range (c (.initial b))) (Set.range (c .terminal)) :=
  arithmeticOneDiagonalAtlas_disjoint_of_original hπ data H m hj u hu _ _
    (arithmeticLabeledAtlas_initial_terminal_disjoint hπ data H m 2 hj (by omega) b)

end FLT.Mazur.WeierstrassDividedDepth
