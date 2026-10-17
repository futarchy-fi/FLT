/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFourthOuterAtlasSystem
public import FLT.Mazur.WeierstrassDividedFourthOuterIdentification
public import FLT.Mazur.WeierstrassDividedThirdEarlierRestriction
public import FLT.Mazur.WeierstrassDividedThirdUnchangedRestriction
public import FLT.Mazur.WeierstrassDividedFourthAtlasNodeRestriction

/-!
# Explicit coefficient maps at the installed fourth outer labels

The earlier and farther corrected labels keep their actual changing-smoothing
coefficient maps. The farther source square retains its normalized orientation.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticFourthOuterAtlasCorrection arithmeticFourthOuterIso arithmeticFourthFartherIso
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
  (m : ℕ)
local notation "S" => arithmeticFourthOuterAtlasRestriction hπ data H j hj u hu

section Earlier
variable (a : ℕ) (ha : a + 2 = j)
local notation "N" => fun k ↦ arithmeticFourthOuterIdentification hπ data H k j hj u hu a ha
local notation "N₃" => fun k ↦ arithmeticThirdEarlierIdentification hπ data H k j hj u hu a ha
local notation "C" => fun k ↦ arithmeticFourthOuterIso hπ data H j hj u hu k

/-- The installed earlier coefficient quotient retains both fourth smoothing drifts. -/
@[reassoc] theorem arithmeticFourthOuterIdentification_restriction (b : Bool) :
    (N m b).hom ≫ S m (.retained ⟨a, by omega⟩ b) =
      arithmeticFourthOuterRestriction hπ data H j hj u hu m b ≫ (N (m + 1) b).hom := by
  have h := arithmeticFourthOuterAtlasCorrection_restriction hπ data H j hj u hu m
    (.retained ⟨a, by omega⟩ b)
  dsimp only at h
  rw [arithmeticFourthOuterAtlasCorrection_earlier hπ data H m j hj u hu a ha b,
    arithmeticFourthOuterAtlasCorrection_earlier hπ data H (m + 1) j hj u hu a ha b] at h
  have hh := congrArg (fun f ↦ (N₃ m b).hom ≫ f) h
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc] at hh
  rw [arithmeticThirdInitialAtlasRestriction_retained,
    arithmeticThirdEarlierIdentification_restriction_assoc, Iso.hom_inv_id_assoc] at hh
  apply (cancel_epi (C m b).hom).mp
  rw [← arithmeticFourthOuterIso_restriction_assoc]
  exact hh
end Earlier

variable (a : ℕ) (ha : a + 3 = j)
local notation "N" => fun k ↦ arithmeticFourthFartherIdentification hπ data H k j hj u hu a ha
local notation "N₃" => fun k ↦ arithmeticThirdUnchangedIdentification hπ data H k j hj u hu
local notation "C" => fun k ↦ arithmeticFourthFartherIso hπ data H j hj u hu k
local notation "O" => fun k ↦ twistedRetainedOrientation data H k

/-- The installed farther coefficient quotient retains its new scalar drift and orientation. -/
@[reassoc] theorem arithmeticFourthFartherIdentification_restriction (b : Bool) :
    (N m b).hom ≫ S m (.retained ⟨a, by omega⟩ b) =
      arithmeticFourthFartherRestriction hπ data H j hj u hu m b ≫ (N (m + 1) b).hom := by
  have h := arithmeticFourthOuterAtlasCorrection_restriction hπ data H j hj u hu m
    (.retained ⟨a, by omega⟩ b)
  dsimp only at h
  rw [arithmeticFourthOuterAtlasCorrection_farther hπ data H m j hj u hu a ha b,
    arithmeticFourthOuterAtlasCorrection_farther hπ data H (m + 1) j hj u hu a ha b] at h
  have hh := congrArg (fun f ↦ (O m b).hom ≫
    (N₃ m ⟨a, by omega⟩ (show a + 2 < j by omega) b).hom ≫ f) h
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc] at hh
  rw [arithmeticThirdInitialAtlasRestriction_retained,
    arithmeticThirdUnchangedIdentification_restriction_assoc, Iso.hom_inv_id_assoc,
    ← twistedRetainedOrientation_restriction_assoc, Iso.hom_inv_id_assoc] at hh
  apply (cancel_epi (C m b).hom).mp
  rw [← arithmeticFourthFartherIso_restriction_assoc]
  exact hh

end FLT.Mazur.WeierstrassDividedDepth
