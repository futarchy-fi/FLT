/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFifthShallowAtlasRestriction
public import FLT.Mazur.WeierstrassDividedFifthShallowJointAtlasRestriction
public import FLT.Mazur.WeierstrassDividedTwoAtlasSystem
public import FLT.Mazur.WeierstrassDividedTwoOpenRestriction

/-!
# Concrete coefficient maps for the entire finite depth-two atlas

All changed nodes use their new smoothing quotients. The initial open keeps
its constructed quotient, and infinity keeps the original coefficient map.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticTwoFiniteInitialIso arithmeticTwoFiniteRetainedIso arithmeticTwoFiniteTerminalIso
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (k : ℕ) (hj : 3 ≤ n)
  (u : Rˣ) (hu : (data ⟨3, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u) (m : ℕ)
local notation "S" => arithmeticTwoFiniteAtlasRestriction hπ data H k hj u hu
local notation "I" => fun l ↦ arithmeticTwoFiniteInitialIso hπ data H k l hj u hu
local notation "L" => fun l ↦ arithmeticTwoFiniteRetainedIso hπ data H k l hj u hu
local notation "F" => fun l ↦ arithmeticTwoFiniteTerminalIso hπ data H k l hj u hu

omit [IsBezout R] in
/-- The finite initial label has its constructed full-open coefficient quotient. -/
theorem arithmeticTwoFiniteAtlasRestriction_initial (b : Bool) :
    S m (.initial b) = arithmeticTwoFiniteInitialRestriction hπ data H hj u hu k m b := by
  change (I m b).inv ≫ arithmeticFifthShallowAtlasRestriction hπ data H hj u hu m (.initial b) ≫
    (I (m + 1) b).hom = _
  rw [arithmeticFifthShallowAtlasRestriction_initial]
  rfl

omit [IsBezout R] in
/-- The first retained node keeps both new smoothing drifts in its explicit quotient. -/
theorem arithmeticTwoFiniteAtlasRestriction_first (b : Bool) :
    S m (.retained (0 : Fin 3) b) =
      arithmeticTwoFiniteRetainedRestriction hπ data H hj u hu k m 0 b := by
  apply (cancel_epi (L m 0 b).hom).mp
  simp only [arithmeticTwoFiniteAtlasRestriction, arithmeticTwoFiniteAtlasCorrection,
    Iso.hom_inv_id_assoc]
  rw [arithmeticFifthShallowAtlasRestriction_neighbor]
  exact arithmeticTwoFiniteRetainedIso_restriction hπ data H hj u hu k m 0 b

omit [IsBezout R] in
/-- The middle predecessor keeps both new smoothing drifts in its explicit quotient. -/
theorem arithmeticTwoFiniteAtlasRestriction_middle (b : Bool) :
    S m (.retained (1 : Fin 3) b) =
      arithmeticTwoFiniteRetainedRestriction hπ data H hj u hu k m 1 b := by
  apply (cancel_epi (L m 1 b).hom).mp
  simp only [arithmeticTwoFiniteAtlasRestriction, arithmeticTwoFiniteAtlasCorrection,
    Iso.hom_inv_id_assoc]
  rw [arithmeticFifthShallowAtlasRestriction_preceding]
  exact arithmeticTwoFiniteRetainedIso_restriction hπ data H hj u hu k m 1 b

/-- The last retained quotient includes the original orientation on both sides. -/
theorem arithmeticTwoFiniteAtlasRestriction_last (b : Bool) :
    S m (.retained (2 : Fin 3) b) =
      arithmeticTwoFiniteRetainedRestriction hπ data H hj u hu k m 2 b := by
  apply (cancel_epi (L m 2 b).hom).mp
  simp only [arithmeticTwoFiniteAtlasRestriction, arithmeticTwoFiniteAtlasCorrection,
    Iso.trans_inv, Iso.symm_inv, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.hom_inv_id_assoc]
  rw [arithmeticFifthShallowAtlasRestriction_last,
    ← twistedRetainedOrientation_restriction_assoc, Iso.hom_inv_id_assoc]
  exact arithmeticTwoFiniteRetainedIso_restriction hπ data H hj u hu k m 2 b

omit [IsBezout R] in
/-- Both closing branches use the coefficient quotient of the same new common terminal. -/
theorem arithmeticTwoFiniteAtlasRestriction_terminal :
    S m .terminal = arithmeticTwoFiniteTerminalRestriction hπ data H hj u hu k m := by
  apply (cancel_epi (F m).hom).mp
  rw [← arithmeticTwoFiniteTerminalIso_restriction]
  have h := arithmeticTwoFiniteAtlasCorrection_restriction hπ data H k hj u hu m .terminal
  change (F m).hom ≫ _ = _ ≫ (F (m + 1)).hom at h
  rw [arithmeticFifthShallowAtlasRestriction_terminal] at h
  exact h

omit [IsBezout R] in
/-- Infinity retains the full original seed coefficient map. -/
theorem arithmeticTwoFiniteAtlasRestriction_infinity :
    S m .infinity = arithmeticFifthShallowAtlasRestriction hπ data H hj u hu m .infinity := by
  change (𝟙 _ ≫ _ ≫ 𝟙 _) = _
  rw [Category.id_comp, Category.comp_id]

end FLT.Mazur.WeierstrassDividedDepth

/-!
# Concrete coefficient maps for the entire diagonal depth-two atlas

The varying correction counts give the actual diagonal smoothing quotients.
The initial open keeps its pullback quotient; infinity keeps its original map.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticTwoFiniteInitialIso arithmeticTwoFiniteRetainedIso arithmeticTwoFiniteTerminalIso
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (hj : 3 ≤ n)
  (u : Rˣ) (hu : (data ⟨3, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u) (m : ℕ)
local notation "S" => arithmeticTwoDiagonalAtlasRestriction hπ data H hj u hu
local notation "I" => fun l ↦ arithmeticTwoFiniteInitialIso hπ data H l l hj u hu
local notation "L" => fun l ↦ arithmeticTwoFiniteRetainedIso hπ data H l l hj u hu
local notation "F" => fun l ↦ arithmeticTwoFiniteTerminalIso hπ data H l l hj u hu

omit [IsBezout R] in
/-- The finite initial label has its constructed full-open coefficient quotient. -/
theorem arithmeticTwoDiagonalAtlasRestriction_initial (b : Bool) :
    S m (.initial b) = arithmeticTwoDiagonalInitialRestriction hπ data H hj u hu m b := by
  change (I m b).inv ≫ arithmeticFifthShallowAtlasRestriction hπ data H hj u hu m (.initial b) ≫
    (I (m + 1) b).hom = _
  rw [arithmeticFifthShallowAtlasRestriction_initial]
  rfl

omit [IsBezout R] in
/-- The first retained node keeps both new smoothing drifts in its explicit quotient. -/
theorem arithmeticTwoDiagonalAtlasRestriction_first (b : Bool) :
    S m (.retained (0 : Fin 3) b) =
      arithmeticTwoDiagonalRetainedRestriction hπ data H hj u hu m 0 b := by
  apply (cancel_epi (L m 0 b).hom).mp
  simp only [arithmeticTwoDiagonalAtlasRestriction, arithmeticTwoDiagonalAtlasCorrection,
    arithmeticTwoFiniteAtlasCorrection,
    Iso.hom_inv_id_assoc]
  rw [arithmeticFifthShallowAtlasRestriction_neighbor]
  exact arithmeticTwoDiagonalRetainedIso_restriction hπ data H hj u hu m 0 b

omit [IsBezout R] in
/-- The middle predecessor keeps both new smoothing drifts in its explicit quotient. -/
theorem arithmeticTwoDiagonalAtlasRestriction_middle (b : Bool) :
    S m (.retained (1 : Fin 3) b) =
      arithmeticTwoDiagonalRetainedRestriction hπ data H hj u hu m 1 b := by
  apply (cancel_epi (L m 1 b).hom).mp
  simp only [arithmeticTwoDiagonalAtlasRestriction, arithmeticTwoDiagonalAtlasCorrection,
    arithmeticTwoFiniteAtlasCorrection,
    Iso.hom_inv_id_assoc]
  rw [arithmeticFifthShallowAtlasRestriction_preceding]
  exact arithmeticTwoDiagonalRetainedIso_restriction hπ data H hj u hu m 1 b

/-- The last retained quotient includes the original orientation on both sides. -/
theorem arithmeticTwoDiagonalAtlasRestriction_last (b : Bool) :
    S m (.retained (2 : Fin 3) b) =
      arithmeticTwoDiagonalRetainedRestriction hπ data H hj u hu m 2 b := by
  apply (cancel_epi (L m 2 b).hom).mp
  simp only [arithmeticTwoDiagonalAtlasRestriction, arithmeticTwoDiagonalAtlasCorrection,
    arithmeticTwoFiniteAtlasCorrection,
    Iso.trans_inv, Iso.symm_inv, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.hom_inv_id_assoc]
  rw [arithmeticFifthShallowAtlasRestriction_last,
    ← twistedRetainedOrientation_restriction_assoc, Iso.hom_inv_id_assoc]
  exact arithmeticTwoDiagonalRetainedIso_restriction hπ data H hj u hu m 2 b

omit [IsBezout R] in
/-- Both closing branches use the coefficient quotient of the same new common terminal. -/
theorem arithmeticTwoDiagonalAtlasRestriction_terminal :
    S m .terminal = arithmeticTwoDiagonalTerminalRestriction hπ data H hj u hu m := by
  apply (cancel_epi (F m).hom).mp
  rw [← arithmeticTwoDiagonalTerminalIso_restriction]
  have h := arithmeticTwoDiagonalAtlasCorrection_restriction hπ data H hj u hu m .terminal
  change (F m).hom ≫ _ = _ ≫ (F (m + 1)).hom at h
  rw [arithmeticFifthShallowAtlasRestriction_terminal] at h
  exact h

omit [IsBezout R] in
/-- Infinity retains the full original seed coefficient map. -/
theorem arithmeticTwoDiagonalAtlasRestriction_infinity :
    S m .infinity = arithmeticFifthShallowAtlasRestriction hπ data H hj u hu m .infinity := by
  change (𝟙 _ ≫ _ ≫ 𝟙 _) = _
  rw [Category.id_comp, Category.comp_id]

end FLT.Mazur.WeierstrassDividedDepth
