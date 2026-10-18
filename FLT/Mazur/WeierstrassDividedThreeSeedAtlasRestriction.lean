/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedThreeSeedAtlasSystem
public import FLT.Mazur.WeierstrassDividedThreeNodeRestriction
public import FLT.Mazur.WeierstrassDividedFifthFartherAtlasRestriction
public import FLT.Mazur.WeierstrassDividedFifthFartherAtlasNodeRestriction
public import FLT.Mazur.WeierstrassDividedFifthFartherAtlasEndRestriction

/-!
# Actual coefficient quotients at every uniform depth-three seed label

The explicit identifications commute with the original quotient. The last
node keeps both orientations until their coefficient square cancels them.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (hj : 4 ≤ n)
  (u : Rˣ) (hu : (data ⟨4, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
  (m : ℕ)
local notation "S" => arithmeticThreeSeedAtlasRestriction hπ data H hj u hu
local notation "J" => fun l ↦ arithmeticThreeSeedIdentification hπ data H l hj u hu
local notation "ρ" => arithmeticFifthFartherAtlasRestriction hπ data H 3 hj u hu rfl

omit [IsBezout R] in
/-- Each retained identification has the actual changing-smoothing coefficient square. -/
@[reassoc] theorem arithmeticThreeSeedRetainedIdentification_restriction
    (i : Fin 4) (b : Bool) :
    (J m (.retained i b)).hom ≫ ρ m (.retained i b) =
      arithmeticThreeSeedRetainedRestriction hπ data H hj u hu m i b ≫
        (J (m + 1) (.retained i b)).hom := by
  fin_cases i
  · exact arithmeticFifthFartherNeighborIdentification_restriction
      hπ data H 3 hj u hu m rfl b
  · exact arithmeticFifthFartherNodeIdentification_restriction
      hπ data H 3 hj u hu rfl m .outer (fun h ↦ FifthDeepNode.noConfusion h) 1 rfl b
  · exact arithmeticFifthFartherNodeIdentification_restriction
      hπ data H 3 hj u hu rfl m .predecessor (fun h ↦ FifthDeepNode.noConfusion h) 2 rfl b
  · simp only [arithmeticThreeSeedIdentification, Iso.trans_hom, Category.assoc]
    rw [arithmeticFifthFartherLastIdentification_restriction,
      ← twistedRetainedOrientation_restriction_assoc]
    rfl

omit [IsBezout R] in
/-- All four transported retained quotients are their full explicit coefficient maps. -/
theorem arithmeticThreeSeedAtlasRestriction_retained (i : Fin 4) (b : Bool) :
    S m (.retained i b) = arithmeticThreeSeedRetainedRestriction hπ data H hj u hu m i b := by
  rw [arithmeticThreeSeedAtlasRestriction,
    ← Category.assoc, arithmeticThreeSeedRetainedIdentification_restriction,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The initial label has the coefficient quotient of the complete original initial open. -/
theorem arithmeticThreeSeedAtlasRestriction_initial (b : Bool) :
    S m (.initial b) = arithmeticFifthFartherOpenRestriction hπ data H 3 hj u hu m b := by
  change (arithmeticFifthFartherIdentification hπ data H m 3 hj u hu rfl b).hom ≫
    ρ m (.initial b) ≫
      (arithmeticFifthFartherIdentification hπ data H (m + 1) 3 hj u hu rfl b).inv = _
  rw [← Category.assoc, arithmeticFifthFartherIdentification_restriction,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

omit [IsBezout R] in
/-- Both closing branches retain the coefficient map of their one full terminal. -/
theorem arithmeticThreeSeedAtlasRestriction_terminal :
    S m .terminal = arithmeticFifthShallowTerminalRestriction hπ data H 3 hj u hu m := by
  change (𝟙 _ ≫ ρ m .terminal ≫ 𝟙 _) = _
  rw [Category.id_comp, Category.comp_id]
  exact arithmeticFifthFartherAtlasRestriction_terminal hπ data H 3 hj u hu rfl m

omit [IsBezout R] in
/-- Infinity retains the original fifth-atlas quotient map. -/
theorem arithmeticThreeSeedAtlasRestriction_infinity :
    S m .infinity = ρ m .infinity := by
  change (𝟙 _ ≫ ρ m .infinity ≫ 𝟙 _) = _
  rw [Category.id_comp, Category.comp_id]

end FLT.Mazur.WeierstrassDividedDepth
