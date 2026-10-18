/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedThreeSeedAtlasRestriction
public import FLT.Mazur.WeierstrassDividedThreeAtlasSystem
public import FLT.Mazur.WeierstrassDividedThreeOpenRestriction

/-!
# Concrete coefficient maps for the entire finite depth-three atlas

All changed nodes use their new smoothing quotients. The initial open keeps
its constructed quotient, and infinity keeps the original coefficient map.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticThreeFiniteInitialIso arithmeticThreeFiniteRetainedIso arithmeticThreeFiniteTerminalIso
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (k : ℕ) (hj : 4 ≤ n)
  (u : Rˣ) (hu : (data ⟨4, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u) (m : ℕ)
local notation "S" => arithmeticThreeFiniteAtlasRestriction hπ data H k hj u hu
local notation "I" => fun l ↦ arithmeticThreeFiniteInitialIso hπ data H k l hj u hu
local notation "L" => fun l ↦ arithmeticThreeFiniteRetainedIso hπ data H k l hj u hu
local notation "F" => fun l ↦ arithmeticThreeFiniteTerminalIso hπ data H k l hj u hu

/-- The finite initial label has its constructed full-open coefficient quotient. -/
theorem arithmeticThreeFiniteAtlasRestriction_initial (b : Bool) :
    S m (.initial b) = arithmeticThreeFiniteInitialRestriction hπ data H hj u hu k m b := by
  change (I m b).inv ≫ arithmeticThreeSeedAtlasRestriction hπ data H hj u hu m (.initial b) ≫
    (I (m + 1) b).hom = _
  rw [arithmeticThreeSeedAtlasRestriction_initial]
  rfl

omit [IsBezout R] in
/-- Every retained node uses the explicit quotient of its complete new smoothing. -/
theorem arithmeticThreeFiniteAtlasRestriction_retained (i : Fin 4) (b : Bool) :
    S m (.retained i b) =
      arithmeticThreeFiniteRetainedRestriction hπ data H hj u hu k m i b := by
  apply (cancel_epi (L m i b).hom).mp
  simp only [arithmeticThreeFiniteAtlasRestriction, arithmeticThreeFiniteAtlasCorrection,
    Iso.hom_inv_id_assoc]
  rw [arithmeticThreeSeedAtlasRestriction_retained]
  exact arithmeticThreeFiniteRetainedIso_restriction hπ data H hj u hu k m i b

omit [IsBezout R] in
/-- Both closing branches use the coefficient quotient of the same new common terminal. -/
theorem arithmeticThreeFiniteAtlasRestriction_terminal :
    S m .terminal = arithmeticThreeFiniteTerminalRestriction hπ data H hj u hu k m := by
  apply (cancel_epi (F m).hom).mp
  rw [← arithmeticThreeFiniteTerminalIso_restriction]
  have h := arithmeticThreeFiniteAtlasCorrection_restriction hπ data H k hj u hu m .terminal
  change (F m).hom ≫ _ = _ ≫ (F (m + 1)).hom at h
  rw [arithmeticThreeSeedAtlasRestriction_terminal] at h
  exact h

omit [IsBezout R] in
/-- Infinity retains the full original seed coefficient map. -/
theorem arithmeticThreeFiniteAtlasRestriction_infinity :
    S m .infinity = arithmeticThreeSeedAtlasRestriction hπ data H hj u hu m .infinity := by
  change (𝟙 _ ≫ _ ≫ 𝟙 _) = _
  rw [Category.id_comp, Category.comp_id]

end FLT.Mazur.WeierstrassDividedDepth

/-!
# Concrete coefficient maps for the entire diagonal depth-three atlas

The varying correction counts give the actual diagonal smoothing quotients.
The initial open keeps its pullback quotient; infinity keeps its original map.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticThreeFiniteInitialIso arithmeticThreeFiniteRetainedIso arithmeticThreeFiniteTerminalIso
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (hj : 4 ≤ n)
  (u : Rˣ) (hu : (data ⟨4, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u) (m : ℕ)
local notation "S" => arithmeticThreeDiagonalAtlasRestriction hπ data H hj u hu
local notation "I" => fun l ↦ arithmeticThreeFiniteInitialIso hπ data H l l hj u hu
local notation "L" => fun l ↦ arithmeticThreeFiniteRetainedIso hπ data H l l hj u hu
local notation "F" => fun l ↦ arithmeticThreeFiniteTerminalIso hπ data H l l hj u hu

/-- The finite initial label has its constructed full-open coefficient quotient. -/
theorem arithmeticThreeDiagonalAtlasRestriction_initial (b : Bool) :
    S m (.initial b) = arithmeticThreeDiagonalInitialRestriction hπ data H hj u hu m b := by
  change (I m b).inv ≫ arithmeticThreeSeedAtlasRestriction hπ data H hj u hu m (.initial b) ≫
    (I (m + 1) b).hom = _
  rw [arithmeticThreeSeedAtlasRestriction_initial]
  rfl

omit [IsBezout R] in
/-- Every retained node uses the explicit quotient of its complete new smoothing. -/
theorem arithmeticThreeDiagonalAtlasRestriction_retained (i : Fin 4) (b : Bool) :
    S m (.retained i b) =
      arithmeticThreeDiagonalRetainedRestriction hπ data H hj u hu m i b := by
  apply (cancel_epi (L m i b).hom).mp
  simp only [arithmeticThreeDiagonalAtlasRestriction, arithmeticThreeDiagonalAtlasCorrection,
    arithmeticThreeFiniteAtlasCorrection,
    Iso.hom_inv_id_assoc]
  rw [arithmeticThreeSeedAtlasRestriction_retained]
  exact arithmeticThreeDiagonalRetainedIso_restriction hπ data H hj u hu m i b

omit [IsBezout R] in
/-- Both closing branches use the coefficient quotient of the same new common terminal. -/
theorem arithmeticThreeDiagonalAtlasRestriction_terminal :
    S m .terminal = arithmeticThreeDiagonalTerminalRestriction hπ data H hj u hu m := by
  apply (cancel_epi (F m).hom).mp
  rw [← arithmeticThreeDiagonalTerminalIso_restriction]
  have h := arithmeticThreeDiagonalAtlasCorrection_restriction hπ data H hj u hu m .terminal
  change (F m).hom ≫ _ = _ ≫ (F (m + 1)).hom at h
  rw [arithmeticThreeSeedAtlasRestriction_terminal] at h
  exact h

omit [IsBezout R] in
/-- Infinity retains the full original seed coefficient map. -/
theorem arithmeticThreeDiagonalAtlasRestriction_infinity :
    S m .infinity = arithmeticThreeSeedAtlasRestriction hπ data H hj u hu m .infinity := by
  change (𝟙 _ ≫ _ ≫ 𝟙 _) = _
  rw [Category.id_comp, Category.comp_id]

end FLT.Mazur.WeierstrassDividedDepth
