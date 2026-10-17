/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFifthShallowAtlasSystem
public import FLT.Mazur.WeierstrassDividedFifthShallowOpenRestriction
public import FLT.Mazur.WeierstrassDividedFourthShallowAtlasRestriction

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
  arithmeticFifthShallowIso arithmeticFifthShallowNeighborIso
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 3 ≤ n)
  (u : Rˣ) (hu : (data ⟨3, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "S" => arithmeticFifthShallowAtlasRestriction hπ data H hj u hu

omit [IsBezout R] in
/-- The installed initial label uses its complete concrete coefficient quotient. -/
theorem arithmeticFifthShallowAtlasRestriction_initial (b : Bool) :
    S m (.initial b) = arithmeticFifthShallowOpenRestriction hπ data H 2 hj u hu m b := by
  apply (cancel_epi (arithmeticFifthShallowIso hπ data H m 2 hj u hu b).hom).mp
  simp only [arithmeticFifthShallowAtlasRestriction, arithmeticFifthShallowAtlasCorrection,
    Iso.trans_inv, Iso.symm_inv, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.hom_inv_id_assoc]
  rw [arithmeticFourthShallowIdentification_restriction_assoc, Iso.hom_inv_id_assoc]
  exact (arithmeticFifthShallowIso_restriction hπ data H 2 hj u hu m b).symm

omit [IsBezout R] in
/-- The installed neighbor label uses its complete concrete coefficient quotient. -/
theorem arithmeticFifthShallowAtlasRestriction_neighbor (b : Bool) :
    S m (.retained (0 : Fin 3) b) =
      arithmeticFifthShallowNeighborRestriction hπ data H 2 hj u hu m b := by
  apply (cancel_epi (arithmeticFifthShallowNeighborIso hπ data H m 2 hj u hu b).hom).mp
  simp only [arithmeticFifthShallowAtlasRestriction, arithmeticFifthShallowAtlasCorrection,
    Iso.trans_inv, Iso.symm_inv, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.hom_inv_id_assoc]
  change (arithmeticFourthShallowNeighborIdentification hπ data H m 2 hj u hu rfl b).hom ≫
      arithmeticFourthShallowAtlasRestriction hπ data H 2 hj u hu m
        (.retained ⟨0, by decide⟩ b) ≫
      (arithmeticFourthShallowNeighborIdentification hπ data H (m + 1) 2 hj u hu rfl b).inv ≫
      (arithmeticFifthShallowNeighborIso hπ data H (m + 1) 2 hj u hu b).hom =
    (arithmeticFifthShallowNeighborIso hπ data H m 2 hj u hu b).hom ≫
      arithmeticFifthShallowNeighborRestriction hπ data H 2 hj u hu m b
  rw [arithmeticFourthShallowNeighborIdentification_restriction_assoc, Iso.hom_inv_id_assoc]
  exact arithmeticFifthShallowNeighborIso_restriction hπ data H 2 hj u hu m b

omit [IsBezout R] in
/-- Infinity keeps the exact fourth quotient map as well as its chart. -/
theorem arithmeticFifthShallowAtlasRestriction_infinity :
    S m .infinity = arithmeticFourthShallowAtlasRestriction hπ data H 2 hj u hu m .infinity := by
  change (𝟙 _ ≫ _ ≫ 𝟙 _) = _
  rw [Category.id_comp, Category.comp_id]

/-- The actual initial global overlap retains the original coefficient quotient at every order. -/
@[reassoc] theorem arithmeticFifthShallowAtlasInitialBoundary_restriction (b : Bool) :
    arithmeticFifthShallowPuncture hπ data H m 2 hj u hu b ≫
        arithmeticFifthShallowAtlasChart hπ data H m hj u hu (.initial b) ≫
          simultaneousTwistedArithmeticRestriction hπ data H m 2 hj u hu =
      closingOverlapRestriction (R := R) (π := π) m ≫
        arithmeticFifthShallowPuncture hπ data H (m + 1) 2 hj u hu b ≫
          arithmeticFifthShallowAtlasChart hπ data H (m + 1) hj u hu (.initial b) := by
  rw [← arithmeticFifthShallowAtlasChart_restriction,
    arithmeticFifthShallowAtlasRestriction_initial, ← Category.assoc,
    arithmeticFifthShallowPuncture_restriction, Category.assoc]

end FLT.Mazur.WeierstrassDividedDepth
