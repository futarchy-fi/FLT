/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroSecondAtlasSystem
public import FLT.Mazur.WeierstrassDividedZeroSecondOpenRestriction
public import FLT.Mazur.WeierstrassDividedZeroFirstAtlasRestriction

/-!
# Concrete coefficient maps for the entire second depth-zero atlas

All changed nodes use their new smoothing quotients. The initial open keeps
its constructed quotient, and infinity keeps the original coefficient map.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticZeroSecondInitialIso arithmeticZeroSecondLastIso arithmeticZeroSecondTerminalIso
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (hj : 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u) (m : ℕ)
local notation "S" => arithmeticZeroSecondAtlasRestriction hπ data H hj u hu
local notation "I" => fun k ↦ arithmeticZeroSecondInitialIso hπ data H k 0 hj u hu
local notation "L" => fun k ↦ arithmeticZeroSecondLastIso hπ data H k 0 hj u hu
local notation "F" => fun k ↦ arithmeticZeroSecondTerminalIso hπ data H k 0 hj u hu

/-- The second initial label has its constructed full-open coefficient quotient. -/
theorem arithmeticZeroSecondAtlasRestriction_initial (b : Bool) :
    S m (.initial b) = arithmeticZeroSecondInitialRestriction hπ data H 0 hj u hu m b := by
  change (I m b).inv ≫ arithmeticZeroFirstAtlasRestriction hπ data H hj u hu m (.initial b) ≫
    (I (m + 1) b).hom = _
  rw [arithmeticZeroFirstAtlasRestriction_initial]
  rfl

omit [IsBezout R] in
/-- The same last node keeps both new smoothing drifts in its explicit quotient. -/
theorem arithmeticZeroSecondAtlasRestriction_last (b : Bool) :
    S m (.retained ⟨0, by omega⟩ b) =
      arithmeticZeroSecondLastRestriction hπ data H 0 hj u hu m b := by
  apply (cancel_epi (L m b).hom).mp
  rw [← arithmeticZeroSecondLastIso_restriction]
  have h := arithmeticZeroSecondAtlasCorrection_restriction hπ data H hj u hu m
    (.retained ⟨0, by omega⟩ b)
  change (L m b).hom ≫ _ = _ ≫ (L (m + 1) b).hom at h
  rw [arithmeticZeroFirstAtlasRestriction_last] at h
  exact h

omit [IsBezout R] in
/-- Both closing branches use the coefficient quotient of the same new common terminal. -/
theorem arithmeticZeroSecondAtlasRestriction_terminal :
    S m .terminal = arithmeticZeroSecondTerminalRestriction hπ data H 0 hj u hu m := by
  apply (cancel_epi (F m).hom).mp
  rw [← arithmeticZeroSecondTerminalIso_restriction]
  have h := arithmeticZeroSecondAtlasCorrection_restriction hπ data H hj u hu m .terminal
  change (F m).hom ≫ _ = _ ≫ (F (m + 1)).hom at h
  rw [arithmeticZeroFirstAtlasRestriction_terminal] at h
  exact h

omit [IsBezout R] in
/-- Infinity still has its original complete arithmetic coefficient map. -/
theorem arithmeticZeroSecondAtlasRestriction_infinity :
    S m .infinity = arithmeticLabeledAtlasRestriction hπ data H m 1 hj .infinity := by
  simpa only [arithmeticZeroSecondAtlasRestriction, arithmeticZeroSecondAtlasCorrection,
    arithmeticZeroSecondAtlasObject, Iso.refl_inv, Iso.refl_hom,
    Category.id_comp, Category.comp_id] using
    arithmeticZeroFirstAtlasRestriction_infinity_coefficient hπ data H hj u hu m

end FLT.Mazur.WeierstrassDividedDepth
