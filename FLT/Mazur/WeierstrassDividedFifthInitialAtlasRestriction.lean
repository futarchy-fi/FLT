/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFifthInitialAtlasSystem
public import FLT.Mazur.WeierstrassDividedFifthInitialOpenRestriction
public import FLT.Mazur.WeierstrassDividedFourthInitialAtlasRestriction

/-!
# Actual coefficient quotients for the fifth initial and neighboring atlas labels

The transported atlas arrows agree with the concrete full open and node maps.
Both Boolean labels and every scalar correction remain in these equalities.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticFifthInitialIso arithmeticFifthInitialNeighborIso
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 2 ≤ n)
  (u : Rˣ) (hu : (data ⟨2, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "S" => arithmeticFifthInitialAtlasRestriction hπ data H hj u hu

omit [IsBezout R] in
/-- The installed initial label uses its complete concrete coefficient quotient. -/
theorem arithmeticFifthInitialAtlasRestriction_initial (b : Bool) :
    S m (.initial b) = arithmeticFifthInitialOpenRestriction hπ data H 1 hj u hu m b := by
  apply (cancel_epi (arithmeticFifthInitialIso hπ data H m 1 hj u hu b).hom).mp
  simp only [arithmeticFifthInitialAtlasRestriction, arithmeticFifthInitialAtlasCorrection,
    Iso.trans_inv, Iso.symm_inv, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.hom_inv_id_assoc]
  rw [arithmeticFourthInitialIdentification_restriction_assoc, Iso.hom_inv_id_assoc]
  exact (arithmeticFifthInitialIso_restriction hπ data H 1 hj u hu m b).symm

omit [IsBezout R] in
/-- The installed neighbor label uses its complete concrete coefficient quotient. -/
theorem arithmeticFifthInitialAtlasRestriction_neighbor (b : Bool) :
    S m (.retained (0 : Fin 2) b) =
      arithmeticFifthInitialNeighborRestriction hπ data H 1 hj u hu m b := by
  apply (cancel_epi (arithmeticFifthInitialNeighborIso hπ data H m 1 hj u hu b).hom).mp
  simp only [arithmeticFifthInitialAtlasRestriction, arithmeticFifthInitialAtlasCorrection,
    Iso.trans_inv, Iso.symm_inv, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.hom_inv_id_assoc]
  change (arithmeticFourthInitialNeighborIdentification hπ data H m 1 hj u hu rfl b).hom ≫
      arithmeticFourthInitialAtlasRestriction hπ data H 1 hj u hu m
        (.retained ⟨0, by decide⟩ b) ≫
      (arithmeticFourthInitialNeighborIdentification hπ data H (m + 1) 1 hj u hu rfl b).inv ≫
      (arithmeticFifthInitialNeighborIso hπ data H (m + 1) 1 hj u hu b).hom =
    (arithmeticFifthInitialNeighborIso hπ data H m 1 hj u hu b).hom ≫
      arithmeticFifthInitialNeighborRestriction hπ data H 1 hj u hu m b
  rw [arithmeticFourthInitialNeighborIdentification_restriction_assoc, Iso.hom_inv_id_assoc]
  exact arithmeticFifthInitialNeighborIso_restriction hπ data H 1 hj u hu m b

omit [IsBezout R] in
/-- Infinity keeps the exact fourth quotient map as well as its chart. -/
theorem arithmeticFifthInitialAtlasRestriction_infinity :
    S m .infinity = arithmeticFourthInitialAtlasRestriction hπ data H 1 hj u hu m .infinity := by
  change (𝟙 _ ≫ _ ≫ 𝟙 _) = _
  rw [Category.id_comp, Category.comp_id]

/-- The actual initial global overlap retains the original coefficient quotient at every order. -/
@[reassoc] theorem arithmeticFifthInitialAtlasInitialBoundary_restriction (b : Bool) :
    arithmeticFifthInitialPuncture hπ data H m 1 hj u hu b ≫
        arithmeticFifthInitialAtlasChart hπ data H m hj u hu (.initial b) ≫
          simultaneousTwistedArithmeticRestriction hπ data H m 1 hj u hu =
      closingOverlapRestriction (R := R) (π := π) m ≫
        arithmeticFifthInitialPuncture hπ data H (m + 1) 1 hj u hu b ≫
          arithmeticFifthInitialAtlasChart hπ data H (m + 1) hj u hu (.initial b) := by
  rw [← arithmeticFifthInitialAtlasChart_restriction,
    arithmeticFifthInitialAtlasRestriction_initial, ← Category.assoc,
    arithmeticFifthInitialPuncture_restriction, Category.assoc]

end FLT.Mazur.WeierstrassDividedDepth
