/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroDiagonalAtlasSystem
public import FLT.Mazur.WeierstrassDividedZeroDiagonalOpenRestriction
public import FLT.Mazur.WeierstrassDividedZeroFifthAtlasRestriction

/-!
# Concrete coefficient maps for the entire diagonal depth-zero atlas

The varying correction counts give the actual diagonal smoothing quotients.
The initial open keeps its pullback quotient; infinity keeps its original map.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticZeroFiniteInitialIso arithmeticZeroFiniteLastIso arithmeticZeroFiniteTerminalIso
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (hj : 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u) (m : ℕ)
local notation "S" => arithmeticZeroDiagonalAtlasRestriction hπ data H hj u hu
local notation "I" => fun l ↦ arithmeticZeroFiniteInitialIso hπ data H l l 0 hj u hu
local notation "L" => fun l ↦ arithmeticZeroFiniteLastIso hπ data H l l 0 hj u hu
local notation "F" => fun l ↦ arithmeticZeroFiniteTerminalIso hπ data H l l 0 hj u hu

/-- The finite initial label has its constructed full-open coefficient quotient. -/
theorem arithmeticZeroDiagonalAtlasRestriction_initial (b : Bool) :
    S m (.initial b) = arithmeticZeroDiagonalInitialRestriction hπ data H 0 hj u hu m b := by
  change (I m b).inv ≫ arithmeticZeroFifthAtlasRestriction hπ data H hj u hu m (.initial b) ≫
    (I (m + 1) b).hom = _
  rw [arithmeticZeroFifthAtlasRestriction_initial]
  rfl

omit [IsBezout R] in
/-- The same last node keeps both new smoothing drifts in its explicit quotient. -/
theorem arithmeticZeroDiagonalAtlasRestriction_last (b : Bool) :
    S m (.retained ⟨0, by omega⟩ b) =
      arithmeticZeroDiagonalLastRestriction hπ data H 0 hj u hu m b := by
  apply (cancel_epi (L m b).hom).mp
  rw [← arithmeticZeroDiagonalLastIso_restriction]
  have h := arithmeticZeroDiagonalAtlasCorrection_restriction hπ data H hj u hu m
    (.retained ⟨0, by omega⟩ b)
  change (L m b).hom ≫ _ = _ ≫ (L (m + 1) b).hom at h
  rw [arithmeticZeroFifthAtlasRestriction_last] at h
  exact h

omit [IsBezout R] in
/-- Both closing branches use the coefficient quotient of the same new common terminal. -/
theorem arithmeticZeroDiagonalAtlasRestriction_terminal :
    S m .terminal = arithmeticZeroDiagonalTerminalRestriction hπ data H 0 hj u hu m := by
  apply (cancel_epi (F m).hom).mp
  rw [← arithmeticZeroDiagonalTerminalIso_restriction]
  have h := arithmeticZeroDiagonalAtlasCorrection_restriction hπ data H hj u hu m .terminal
  change (F m).hom ≫ _ = _ ≫ (F (m + 1)).hom at h
  rw [arithmeticZeroFifthAtlasRestriction_terminal] at h
  exact h

omit [IsBezout R] in
/-- Infinity still has its original complete arithmetic coefficient map. -/
theorem arithmeticZeroDiagonalAtlasRestriction_infinity :
    S m .infinity = arithmeticLabeledAtlasRestriction hπ data H m 1 hj .infinity := by
  simpa only [arithmeticZeroDiagonalAtlasRestriction, arithmeticZeroDiagonalAtlasCorrection,
    arithmeticZeroDiagonalAtlasObject, arithmeticZeroFiniteAtlasCorrection,
    arithmeticZeroFiniteAtlasObject, Iso.refl_inv, Iso.refl_hom,
    Category.id_comp, Category.comp_id] using
    arithmeticZeroFifthAtlasRestriction_infinity hπ data H hj u hu m

end FLT.Mazur.WeierstrassDividedDepth
