/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFifthInitialAtlasSystem
public import FLT.Mazur.WeierstrassDividedFifthInitialLastRestriction
public import FLT.Mazur.WeierstrassDividedFifthShallowTerminalGeometry
public import FLT.Mazur.WeierstrassDividedFourthInitialAtlasRestriction

/-!
# Actual coefficient quotients for the fifth interior and terminal atlas labels

The transported atlas arrows agree with the concrete full node maps.
Both Boolean labels and every scalar correction remain in these equalities.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticFifthInitialLastOrientedIso
  arithmeticFifthShallowTerminalIso
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 2 ≤ n)
  (u : Rˣ) (hu : (data ⟨2, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "S" => arithmeticFifthInitialAtlasRestriction hπ data H hj u hu

omit [IsBezout R] in
/-- The installed last label uses its complete concrete coefficient quotient. -/
theorem arithmeticFifthInitialAtlasRestriction_last (b : Bool) :
    S m (.retained (1 : Fin 2) b) = closingNormalizedRestriction data H m := by
  apply (cancel_epi (arithmeticFifthInitialLastOrientedIso hπ data H m 1 hj u hu b).hom).mp
  simp only [arithmeticFifthInitialAtlasRestriction, arithmeticFifthInitialAtlasCorrection,
    Iso.trans_inv, Iso.symm_inv, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.hom_inv_id_assoc]
  change (arithmeticFourthInitialLastIdentification hπ data H m 1 hj u hu b).hom ≫
      arithmeticFourthInitialAtlasRestriction hπ data H 1 hj u hu m
        (.retained ⟨1, by decide⟩ b) ≫
      (arithmeticFourthInitialLastIdentification hπ data H (m + 1) 1 hj u hu b).inv ≫
      (arithmeticFifthInitialLastOrientedIso hπ data H (m + 1) 1 hj u hu b).hom =
    (arithmeticFifthInitialLastOrientedIso hπ data H m 1 hj u hu b).hom ≫
      closingNormalizedRestriction data H m
  rw [arithmeticFourthInitialLastIdentification_restriction_assoc, Iso.hom_inv_id_assoc]
  exact arithmeticFifthInitialLastOrientedIso_restriction hπ data H 1 hj u hu m b

omit [IsBezout R] in
/-- The installed terminal uses the exact fifth rebased smoothing's coefficient quotient. -/
theorem arithmeticFifthInitialAtlasRestriction_terminal :
    S m .terminal = arithmeticFifthShallowTerminalRestriction hπ data H 1 hj u hu m := by
  apply (cancel_epi (arithmeticFifthShallowTerminalIso hπ data H m 1 hj u hu).hom).mp
  simp only [arithmeticFifthInitialAtlasRestriction, arithmeticFifthInitialAtlasCorrection,
    Iso.hom_inv_id_assoc]
  change arithmeticFourthAtlasRestriction hπ data H 1 hj u hu m .terminal ≫ _ = _
  rw [arithmeticFourthAtlasRestriction_terminal]
  exact arithmeticFifthShallowTerminalIso_restriction hπ data H 1 hj u hu m

end FLT.Mazur.WeierstrassDividedDepth
