/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOneFiniteAtlasSystem
public import FLT.Mazur.WeierstrassDividedOneFiniteOpenRestriction
public import FLT.Mazur.WeierstrassDividedFifthInitialAtlasRestriction
public import FLT.Mazur.WeierstrassDividedFifthInitialJointAtlasRestriction

/-!
# Concrete coefficient maps for the entire finite depth-one atlas

All changed nodes use their new smoothing quotients. The initial open keeps
its constructed quotient, and infinity keeps the original coefficient map.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticOneFiniteInitialIso arithmeticOneFiniteRetainedIso arithmeticOneFiniteTerminalIso
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (k : ℕ) (hj : 2 ≤ n)
  (u : Rˣ) (hu : (data ⟨2, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u) (m : ℕ)
local notation "S" => arithmeticOneFiniteAtlasRestriction hπ data H k hj u hu
local notation "I" => fun l ↦ arithmeticOneFiniteInitialIso hπ data H k l hj u hu
local notation "L" => fun l ↦ arithmeticOneFiniteRetainedIso hπ data H k l hj u hu
local notation "F" => fun l ↦ arithmeticOneFiniteTerminalIso hπ data H k l hj u hu

omit [IsBezout R] in
/-- The finite initial label has its constructed full-open coefficient quotient. -/
theorem arithmeticOneFiniteAtlasRestriction_initial (b : Bool) :
    S m (.initial b) = arithmeticOneFiniteInitialRestriction hπ data H hj u hu k m b := by
  change (I m b).inv ≫ arithmeticFifthInitialAtlasRestriction hπ data H hj u hu m (.initial b) ≫
    (I (m + 1) b).hom = _
  rw [arithmeticFifthInitialAtlasRestriction_initial]
  rfl

omit [IsBezout R] in
/-- The first retained node keeps both new smoothing drifts in its explicit quotient. -/
theorem arithmeticOneFiniteAtlasRestriction_first (b : Bool) :
    S m (.retained (0 : Fin 2) b) =
      arithmeticOneFiniteRetainedRestriction hπ data H hj u hu k m 0 b := by
  apply (cancel_epi (L m 0 b).hom).mp
  simp only [arithmeticOneFiniteAtlasRestriction, arithmeticOneFiniteAtlasCorrection,
    Iso.hom_inv_id_assoc]
  rw [arithmeticFifthInitialAtlasRestriction_neighbor]
  exact arithmeticOneFiniteRetainedIso_restriction hπ data H hj u hu k m 0 b

omit [IsBezout R] in
/-- The last retained quotient includes the original orientation on both sides. -/
theorem arithmeticOneFiniteAtlasRestriction_last (b : Bool) :
    S m (.retained (1 : Fin 2) b) =
      arithmeticOneFiniteRetainedRestriction hπ data H hj u hu k m 1 b := by
  apply (cancel_epi (L m 1 b).hom).mp
  simp only [arithmeticOneFiniteAtlasRestriction, arithmeticOneFiniteAtlasCorrection,
    Iso.trans_inv, Iso.symm_inv, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.hom_inv_id_assoc]
  rw [arithmeticFifthInitialAtlasRestriction_last,
    ← twistedRetainedOrientation_restriction_assoc, Iso.hom_inv_id_assoc]
  exact arithmeticOneFiniteRetainedIso_restriction hπ data H hj u hu k m 1 b

omit [IsBezout R] in
/-- Both closing branches use the coefficient quotient of the same new common terminal. -/
theorem arithmeticOneFiniteAtlasRestriction_terminal :
    S m .terminal = arithmeticOneFiniteTerminalRestriction hπ data H hj u hu k m := by
  apply (cancel_epi (F m).hom).mp
  rw [← arithmeticOneFiniteTerminalIso_restriction]
  have h := arithmeticOneFiniteAtlasCorrection_restriction hπ data H k hj u hu m .terminal
  change (F m).hom ≫ _ = _ ≫ (F (m + 1)).hom at h
  rw [arithmeticFifthInitialAtlasRestriction_terminal] at h
  exact h

omit [IsBezout R] in
/-- Infinity retains the full original seed coefficient map. -/
theorem arithmeticOneFiniteAtlasRestriction_infinity :
    S m .infinity = arithmeticFifthInitialAtlasRestriction hπ data H hj u hu m .infinity := by
  change (𝟙 _ ≫ _ ≫ 𝟙 _) = _
  rw [Category.id_comp, Category.comp_id]

end FLT.Mazur.WeierstrassDividedDepth
