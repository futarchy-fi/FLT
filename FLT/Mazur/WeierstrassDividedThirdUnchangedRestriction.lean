/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedThirdEarlierRestriction
public import FLT.Mazur.WeierstrassDividedThirdEarlierAdjacent

/-!
# Coefficient restriction of the unchanged third labels

The retained labels beyond the third correction keep their original normalized
coefficient quotient. This supplies the source square of the farther fourth factor.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticThirdAtlasCorrection arithmeticThirdEarlierOrientedIso
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
  (m : ℕ)
local notation "S₂" => arithmeticSecondJointAtlasRestriction hπ data H j hj u hu
local notation "N₂" => fun k ↦ arithmeticSecondJointEarlierIdentification hπ data H k j hj u hu
local notation "ρ" => closingNormalizedRestriction data H m

local notation "S" => arithmeticThirdAtlasRestriction hπ data H j hj u hu
local notation "N" => fun k ↦ arithmeticThirdUnchangedIdentification hπ data H k j hj u hu

/-- Every unaffected third label retains the original normalized coefficient map. -/
@[reassoc] theorem arithmeticThirdUnchangedIdentification_restriction
    (i : Fin (j + 1)) (hi : i.val + 2 < j) (b : Bool) :
    (N m i hi b).hom ≫ S m (.retained i b) = ρ ≫ (N (m + 1) i hi b).hom := by
  have h := arithmeticThirdAtlasCorrection_restriction hπ data H j hj u hu m (.retained i b)
  dsimp only at h
  have hh := congrArg (fun f ↦ (N₂ m i (show i.val + 1 < j by omega) b).hom ≫ f) h
  rw [arithmeticSecondJointEarlierIdentification_restriction_assoc] at hh
  simpa only [arithmeticThirdAtlasCorrection, arithmeticThirdUnchangedIdentification,
    show ¬i.val + 1 = j by omega, show ¬i.val + 2 = j by omega,
    show ¬i.val = j by omega, ↓reduceDIte, ↓reduceIte, Iso.trans_hom,
    Iso.refl_hom, Category.id_comp, Category.assoc] using hh

end FLT.Mazur.WeierstrassDividedDepth
