/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroDiagonalInitialIntersection
public import FLT.Mazur.WeierstrassDividedArithmeticLabeledSeparation
public import FLT.Mazur.WeierstrassDividedArithmeticLabeledEarlierTerminal

/-!
# Empty intersections of the complete corrected depth-zero atlas

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
  arithmeticZeroFiniteAtlasIso simultaneousTwistedArithmeticIso

/-- A full empty scheme pullback excludes all common chart points. -/
theorem emptyPullback_disjoint_ranges {A B X : Scheme} {f : A ⟶ X} {g : B ⟶ X}
    (h : IsPullback (Scheme.emptyTo A) (Scheme.emptyTo B) f g) :
    Disjoint (Set.range f) (Set.range g) := by
  apply Set.disjoint_left.mpr
  rintro z ⟨a, ha⟩ ⟨b, hb⟩
  obtain ⟨w, _, _⟩ := Scheme.exists_preimage_of_isPullback h a b (ha.trans hb.symm)
  exact isEmptyElim w

/-- Disjoint complete chart images stay disjoint under full chart and global isomorphisms. -/
theorem fullChartIso_disjoint {A B X A' B' X' : Scheme}
    {f : A ⟶ X} {g : B ⟶ X} {f' : A' ⟶ X'} {g' : B' ⟶ X'}
    (e : A ≅ A') (d : B ≅ B') (t : X ≅ X')
    (hf : e.hom ≫ f' = f ≫ t.hom) (hg : d.hom ≫ g' = g ≫ t.hom)
    (h : Disjoint (Set.range f) (Set.range g)) :
    Disjoint (Set.range f') (Set.range g') := by
  apply Set.disjoint_left.mpr
  rintro z ⟨a, ha⟩ ⟨b, hb⟩
  obtain ⟨a, rfl⟩ := e.hom.homeomorph.surjective a
  obtain ⟨b, rfl⟩ := d.hom.homeomorph.surjective b
  have he : t.hom (f a) = t.hom (g b) := by
    change (f ≫ t.hom) a = (g ≫ t.hom) b
    rw [← hf, ← hg]
    exact ha.trans hb.symm
  exact Set.disjoint_left.mp h ⟨a, rfl⟩ ⟨b, (t.hom.homeomorph.injective he).symm⟩

variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "c" => arithmeticZeroDiagonalAtlasChart hπ data H m hj u hu
local notation "E" => arithmeticZeroFiniteAtlasIso hπ data H m m hj u hu
local notation "G" => simultaneousTwistedArithmeticIso hπ data H m 0 hj u hu

/-- All original disjoint labeled chart pairs remain disjoint in the full diagonal atlas. -/
theorem arithmeticZeroDiagonalAtlas_disjoint_of_original (i j : ArithmeticChartLabel 1)
    (h : Disjoint (Set.range (arithmeticLabeledAtlasMap hπ data H m 1 hj i))
      (Set.range (arithmeticLabeledAtlasMap hπ data H m 1 hj j))) :
    Disjoint (Set.range (c i)) (Set.range (c j)) :=
  fullChartIso_disjoint (E i) (E j) G
    (arithmeticZeroFiniteAtlasIso_chart hπ data H m m hj u hu i).symm
    (arithmeticZeroFiniteAtlasIso_chart hπ data H m m hj u hu j).symm h

/-- Neither full corrected retained node meets the original infinity chart. -/
theorem arithmeticZeroDiagonalAtlas_retained_infinity_disjoint (b : Bool) :
    Disjoint (Set.range (c (.retained ⟨0, by omega⟩ b))) (Set.range (c .infinity)) :=
  arithmeticZeroDiagonalAtlas_disjoint_of_original hπ data H m hj u hu _ _
    (arithmeticLabeledAtlas_retained_infinity_disjoint hπ data H m 1 hj ⟨0, by omega⟩ b
      (by omega))

/-- An initial chart misses the full retained node of the opposite label. -/
theorem arithmeticZeroDiagonalAtlas_initial_crossLabel_disjoint
    (b d : Bool) (hbd : b ≠ d) :
    Disjoint (Set.range (c (.initial b))) (Set.range (c (.retained ⟨0, by omega⟩ d))) :=
  arithmeticZeroDiagonalAtlas_disjoint_of_original hπ data H m hj u hu _ _
    (emptyPullback_disjoint_ranges
      (arithmeticLabeledAtlas_initial_crossLabel_isPullback hπ data H m 1 hj (by omega) b d hbd))

/-- The two complete retained nodes remain disjoint after every finite correction. -/
theorem arithmeticZeroDiagonalAtlas_retained_disjoint :
    Disjoint (Set.range (c (.retained ⟨0, by omega⟩ false)))
      (Set.range (c (.retained ⟨0, by omega⟩ true))) :=
  arithmeticZeroDiagonalAtlas_disjoint_of_original hπ data H m hj u hu _ _
    (emptyPullback_disjoint_ranges
      (arithmeticLabeledAtlas_sameDepth_isPullback hπ data H m 1 hj ⟨0, by omega⟩
        false true Bool.false_ne_true))

/-- The complete terminal remains disjoint from the full infinity chart. -/
theorem arithmeticZeroDiagonalAtlas_terminal_infinity_disjoint :
    Disjoint (Set.range (c .terminal)) (Set.range (c .infinity)) :=
  arithmeticZeroDiagonalAtlas_disjoint_of_original hπ data H m hj u hu _ _
    (arithmeticLabeledAtlas_terminal_infinity_disjoint hπ data H m 1 hj (by omega))

/-- Neither complete original initial open meets the common terminal. -/
theorem arithmeticZeroDiagonalAtlas_initial_terminal_disjoint (b : Bool) :
    Disjoint (Set.range (c (.initial b))) (Set.range (c .terminal)) :=
  arithmeticZeroDiagonalAtlas_disjoint_of_original hπ data H m hj u hu _ _
    (arithmeticLabeledAtlas_initial_terminal_disjoint hπ data H m 1 hj (by omega) b)

end FLT.Mazur.WeierstrassDividedDepth
