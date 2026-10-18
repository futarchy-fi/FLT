/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroFourthAtlasSystem
public import FLT.Mazur.WeierstrassDividedZeroFourthOpenRestriction
public import FLT.Mazur.WeierstrassDividedZeroThirdAtlasRestriction

/-!
# Concrete coefficient maps for the entire fourth depth-zero atlas

All changed nodes use their new smoothing quotients. The initial open keeps
its constructed quotient, and infinity keeps the original coefficient map.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticZeroFourthInitialIso arithmeticZeroFourthLastIso arithmeticZeroFourthTerminalIso
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (hj : 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u) (m : ℕ)
local notation "S" => arithmeticZeroFourthAtlasRestriction hπ data H hj u hu
local notation "I" => fun k ↦ arithmeticZeroFourthInitialIso hπ data H k 0 hj u hu
local notation "L" => fun k ↦ arithmeticZeroFourthLastIso hπ data H k 0 hj u hu
local notation "F" => fun k ↦ arithmeticZeroFourthTerminalIso hπ data H k 0 hj u hu

/-- The fourth initial label has its constructed full-open coefficient quotient. -/
theorem arithmeticZeroFourthAtlasRestriction_initial (b : Bool) :
    S m (.initial b) = arithmeticZeroFourthInitialRestriction hπ data H 0 hj u hu m b := by
  change (I m b).inv ≫ arithmeticZeroThirdAtlasRestriction hπ data H hj u hu m (.initial b) ≫
    (I (m + 1) b).hom = _
  rw [arithmeticZeroThirdAtlasRestriction_initial]
  rfl

omit [IsBezout R] in
/-- The same last node keeps both new smoothing drifts in its explicit quotient. -/
theorem arithmeticZeroFourthAtlasRestriction_last (b : Bool) :
    S m (.retained ⟨0, by omega⟩ b) =
      arithmeticZeroFourthLastRestriction hπ data H 0 hj u hu m b := by
  apply (cancel_epi (L m b).hom).mp
  rw [← arithmeticZeroFourthLastIso_restriction]
  have h := arithmeticZeroFourthAtlasCorrection_restriction hπ data H hj u hu m
    (.retained ⟨0, by omega⟩ b)
  change (L m b).hom ≫ _ = _ ≫ (L (m + 1) b).hom at h
  rw [arithmeticZeroThirdAtlasRestriction_last] at h
  exact h

omit [IsBezout R] in
/-- Both closing branches use the coefficient quotient of the same new common terminal. -/
theorem arithmeticZeroFourthAtlasRestriction_terminal :
    S m .terminal = arithmeticZeroFourthTerminalRestriction hπ data H 0 hj u hu m := by
  apply (cancel_epi (F m).hom).mp
  rw [← arithmeticZeroFourthTerminalIso_restriction]
  have h := arithmeticZeroFourthAtlasCorrection_restriction hπ data H hj u hu m .terminal
  change (F m).hom ≫ _ = _ ≫ (F (m + 1)).hom at h
  rw [arithmeticZeroThirdAtlasRestriction_terminal] at h
  exact h

omit [IsBezout R] in
/-- Infinity still has its original complete arithmetic coefficient map. -/
theorem arithmeticZeroFourthAtlasRestriction_infinity :
    S m .infinity = arithmeticLabeledAtlasRestriction hπ data H m 1 hj .infinity := by
  simpa only [arithmeticZeroFourthAtlasRestriction, arithmeticZeroFourthAtlasCorrection,
    arithmeticZeroFourthAtlasObject, Iso.refl_inv, Iso.refl_hom,
    Category.id_comp, Category.comp_id] using
    arithmeticZeroThirdAtlasRestriction_infinity hπ data H hj u hu m

end FLT.Mazur.WeierstrassDividedDepth
