/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFifthShallowAtlasSystem
public import FLT.Mazur.WeierstrassDividedFifthShallowJointNodeRestriction
public import FLT.Mazur.WeierstrassDividedFifthShallowTerminalGeometry
public import FLT.Mazur.WeierstrassDividedFourthShallowJointAtlasRestriction

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
  arithmeticFifthShallowLastOrientedIso arithmeticFifthShallowPrecedingIso
  arithmeticFifthShallowTerminalIso
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 3 ≤ n)
  (u : Rˣ) (hu : (data ⟨3, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "S" => arithmeticFifthShallowAtlasRestriction hπ data H hj u hu

/-- The installed last label uses its complete concrete coefficient quotient. -/
theorem arithmeticFifthShallowAtlasRestriction_last (b : Bool) :
    S m (.retained (2 : Fin 3) b) = closingNormalizedRestriction data H m := by
  apply (cancel_epi (arithmeticFifthShallowLastOrientedIso hπ data H m 2 hj u hu b).hom).mp
  simp only [arithmeticFifthShallowAtlasRestriction, arithmeticFifthShallowAtlasCorrection,
    Iso.trans_inv, Iso.symm_inv, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.hom_inv_id_assoc]
  change (arithmeticFourthShallowLastIdentification hπ data H m 2 hj u hu b).hom ≫
      arithmeticFourthShallowAtlasRestriction hπ data H 2 hj u hu m
        (.retained ⟨2, by decide⟩ b) ≫
      (arithmeticFourthShallowLastIdentification hπ data H (m + 1) 2 hj u hu b).inv ≫
      (arithmeticFifthShallowLastOrientedIso hπ data H (m + 1) 2 hj u hu b).hom =
    (arithmeticFifthShallowLastOrientedIso hπ data H m 2 hj u hu b).hom ≫
      closingNormalizedRestriction data H m
  rw [arithmeticFourthShallowLastIdentification_restriction_assoc, Iso.hom_inv_id_assoc]
  exact arithmeticFifthShallowLastOrientedIso_restriction hπ data H 2 hj u hu m b

omit [IsBezout R] in
/-- The installed preceding label uses its complete concrete coefficient quotient. -/
theorem arithmeticFifthShallowAtlasRestriction_preceding (b : Bool) :
    S m (.retained (1 : Fin 3) b) =
      arithmeticFifthShallowPrecedingRestriction hπ data H 2 hj u hu m b := by
  apply (cancel_epi (arithmeticFifthShallowPrecedingIso hπ data H m 2 hj u hu b).hom).mp
  simp only [arithmeticFifthShallowAtlasRestriction, arithmeticFifthShallowAtlasCorrection,
    Iso.trans_inv, Iso.symm_inv, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.hom_inv_id_assoc]
  change (arithmeticFourthShallowPrecedingIdentification
      hπ data H m 2 hj u hu 1 rfl (by decide) b).hom ≫
      arithmeticFourthShallowAtlasRestriction hπ data H 2 hj u hu m
        (.retained ⟨1, by decide⟩ b) ≫
      (arithmeticFourthShallowPrecedingIdentification
        hπ data H (m + 1) 2 hj u hu 1 rfl (by decide) b).inv ≫
      (arithmeticFifthShallowPrecedingIso hπ data H (m + 1) 2 hj u hu b).hom =
    (arithmeticFifthShallowPrecedingIso hπ data H m 2 hj u hu b).hom ≫
      arithmeticFifthShallowPrecedingRestriction hπ data H 2 hj u hu m b
  rw [arithmeticFourthShallowPrecedingIdentification_restriction_assoc, Iso.hom_inv_id_assoc]
  exact arithmeticFifthShallowPrecedingIso_restriction hπ data H 2 hj u hu m b

omit [IsBezout R] in
/-- The installed terminal uses the exact fifth rebased smoothing's coefficient quotient. -/
theorem arithmeticFifthShallowAtlasRestriction_terminal :
    S m .terminal = arithmeticFifthShallowTerminalRestriction hπ data H 2 hj u hu m := by
  apply (cancel_epi (arithmeticFifthShallowTerminalIso hπ data H m 2 hj u hu).hom).mp
  simp only [arithmeticFifthShallowAtlasRestriction, arithmeticFifthShallowAtlasCorrection,
    Iso.hom_inv_id_assoc]
  rw [arithmeticFourthShallowAtlasRestriction_terminal]
  exact arithmeticFifthShallowTerminalIso_restriction hπ data H 2 hj u hu m

end FLT.Mazur.WeierstrassDividedDepth
