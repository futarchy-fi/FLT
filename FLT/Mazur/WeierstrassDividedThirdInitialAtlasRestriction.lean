/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedThirdInitialAtlasSystem
public import FLT.Mazur.WeierstrassDividedThirdInitialAtlasEdge
public import FLT.Mazur.WeierstrassDividedThirdInitialRestriction

/-!
# Installed initial restrictions are the full original coefficient maps

The unchanged third initial label has its original coefficient restriction.
After the depth-one correction, the installed restriction is identified with
the constructed quotient of the full corrected initial open.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticThirdInitialAtlasCorrection arithmeticFullInitialNodeQuotient
  arithmeticSecondJointAtlasRestriction
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
  (m : ℕ)

/-- Before the extra initial correction, the full original initial coefficient map remains. -/
theorem arithmeticThirdAtlasRestriction_initial (b : Bool) :
    arithmeticThirdAtlasRestriction hπ data H j hj u hu m (.initial b) =
      arithmeticFullInitialNodeQuotient R π m W (π ^ 1) := by
  change (𝟙 _ ≫ arithmeticSecondJointAtlasRestriction
    hπ data H j hj u hu m (.initial b) ≫ 𝟙 _) = _
  rw [Category.id_comp, Category.comp_id]
  simpa only [arithmeticLabeledAtlasRestriction] using
    arithmeticSecondJointAtlasRestriction_initial hπ data H j hj u hu m b

variable (ha : 1 = j)
local notation "J" => fun k ↦ arithmeticThirdInitialIdentification hπ data H k j hj u hu ha
local notation "I" => fun k ↦ arithmeticThirdInitialIso hπ data H k j hj u hu
local notation "S" => arithmeticThirdInitialAtlasRestriction hπ data H j hj u hu

/-- The installed corrected initial label has exactly the original transported quotient. -/
@[reassoc] theorem arithmeticThirdInitialIdentification_restriction (b : Bool) :
    (J m b).hom ≫ S m (.initial b) =
      arithmeticThirdInitialRestriction hπ data H j hj u hu m b ≫ (J (m + 1) b).hom := by
  have h := arithmeticThirdInitialAtlasCorrection_restriction
    hπ data H j hj u hu m (.initial b)
  dsimp only at h
  rw [arithmeticThirdInitialAtlasCorrection_initial hπ data H m j hj u hu ha b,
    arithmeticThirdInitialAtlasCorrection_initial hπ data H (m + 1) j hj u hu ha b,
    Iso.trans_hom, Iso.trans_hom, Category.assoc,
    arithmeticThirdAtlasRestriction_initial] at h
  apply (cancel_epi (I m b).hom).mp
  rw [arithmeticThirdInitialIso_restriction_assoc]
  exact h

end FLT.Mazur.WeierstrassDividedDepth
