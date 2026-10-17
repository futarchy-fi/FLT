/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFifthDeepInputIdentification
public import FLT.Mazur.WeierstrassDividedFifthDeepNodeRestriction
public import FLT.Mazur.WeierstrassDividedFourthOuterAtlasRestriction

/-!
# Concrete coefficient quotients at the three fifth input labels

The previous fourth restrictions agree with the explicit coefficient maps on
all three paired input smoothings, including the retained predecessor.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticFourthOuterAtlasCorrection arithmeticFourthPrecedingIso
variable {R : Type} [CommRing R] [IsDomain R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
  (m : ℕ)
local notation "S" => arithmeticFourthOuterAtlasRestriction hπ data H j hj u hu

section Predecessor
variable (a : ℕ) (ha : a + 1 = j) (hj₂ : 2 ≤ j)
local notation "N" => fun k ↦
  arithmeticFourthOuterPrecedingIdentification hπ data H k j hj u hu a ha hj₂
local notation "N₃" => fun k ↦
  arithmeticThirdPrecedingIdentification hπ data H k j hj u hu a ha
local notation "C" => fun k ↦ arithmeticFourthPrecedingIso hπ data H k j hj u hu

/-- The retained fourth predecessor has its complete changing-smoothing coefficient map. -/
@[reassoc] theorem arithmeticFifthDeepPredecessorInput_restriction (b : Bool) :
    (N m b).hom ≫ S m (.retained ⟨a, by omega⟩ b) =
      arithmeticFourthPrecedingRestriction hπ data H j hj u hu m b ≫ (N (m + 1) b).hom := by
  have h := arithmeticFourthOuterAtlasCorrection_restriction hπ data H j hj u hu m
    (.retained ⟨a, by omega⟩ b)
  dsimp only at h
  rw [arithmeticFourthOuterAtlasCorrection_preceding hπ data H m j hj u hu a ha hj₂ b,
    arithmeticFourthOuterAtlasCorrection_preceding hπ data H (m + 1) j hj u hu a ha hj₂ b] at h
  have hh := congrArg (fun f ↦ (N₃ m b).hom ≫ f) h
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc] at hh
  rw [arithmeticThirdInitialAtlasRestriction_retained,
    arithmeticThirdPrecedingIdentification_restriction_assoc, Iso.hom_inv_id_assoc] at hh
  apply (cancel_epi (C m b).hom).mp
  rw [← arithmeticFourthPrecedingIso_restriction_assoc]
  exact hh
end Predecessor

variable (hj₄ : 4 ≤ j) (v : FifthDeepNode) (a : ℕ)
  (ha : a + fifthDeepOffset v = j)
local notation "D" => fun k ↦
  arithmeticFifthDeepInputIdentification hπ data H k j hj u hu hj₄ v a ha

/-- Every installed fifth input uses exactly its actual fourth coefficient quotient. -/
@[reassoc] theorem arithmeticFifthDeepInputIdentification_restriction (b : Bool) :
    (D m b).hom ≫ S m (.retained ⟨a, by cases v <;> simp_all [fifthDeepOffset] <;> omega⟩ b) =
      arithmeticFifthDeepInputRestriction hπ data H j hj u hu m v b ≫ (D (m + 1) b).hom := by
  cases v
  · exact arithmeticFifthDeepPredecessorInput_restriction
      hπ data H j hj u hu m a ha (by omega) b
  · exact arithmeticFourthOuterIdentification_restriction hπ data H j hj u hu m a ha b
  · exact arithmeticFourthFartherIdentification_restriction hπ data H j hj u hu m a ha b

end FLT.Mazur.WeierstrassDividedDepth
