/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFifthFartherInputIdentification
public import FLT.Mazur.WeierstrassDividedFifthDeepInputRestriction
public import FLT.Mazur.WeierstrassDividedFourthFartherInitial
public import FLT.Mazur.WeierstrassDividedThirdInitialAtlasRestriction
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

variable (hj₃ : 3 ≤ j) (v : FifthDeepNode) (a : ℕ)
  (ha : a + fifthDeepOffset v = j)
local notation "D" => fun k ↦
  arithmeticFifthFartherInputIdentification hπ data H k j hj u hu hj₃ v a ha

/-- Every installed fifth input uses exactly its actual fourth coefficient quotient. -/
@[reassoc] theorem arithmeticFifthFartherInputIdentification_restriction (b : Bool) :
    (D m b).hom ≫ S m (.retained ⟨a, by cases v <;> simp_all [fifthDeepOffset] <;> omega⟩ b) =
      arithmeticFifthDeepInputRestriction hπ data H j hj u hu m v b ≫ (D (m + 1) b).hom := by
  cases v
  · exact arithmeticFifthDeepPredecessorInput_restriction
      hπ data H j hj u hu m a ha (by omega) b
  · exact arithmeticFourthOuterIdentification_restriction hπ data H j hj u hu m a ha b
  · exact arithmeticFourthFartherIdentification_restriction hπ data H j hj u hu m a ha b

section Initial
variable [IsBezout R] (ha₃ : 3 = j)
local notation "J" => fun k ↦
  arithmeticFourthOuterInitialThreeIdentification hπ data H k j hj u hu ha₃

/-- The unchanged depth-three initial source retains its full original coefficient quotient. -/
@[reassoc] theorem arithmeticFifthFartherInitialInput_restriction (b : Bool) :
    (J m b).hom ≫ S m (.initial b) =
      arithmeticFullInitialNodeQuotient R π m W (π ^ 1) ≫ (J (m + 1) b).hom := by
  apply (cancel_mono
    (arithmeticFourthOuterAtlasChart hπ data H (m + 1) j hj u hu (.initial b))).mp
  rw [Category.assoc, arithmeticFourthOuterAtlasChart_restriction,
    ← Category.assoc, arithmeticFourthOuterAtlasChart_initial_three,
    Category.assoc, arithmeticFourthOuterAtlasChart_initial_three]
  have h := arithmeticThirdAtlasChart_restriction hπ data H j hj u hu m (.initial b)
  rw [arithmeticThirdAtlasRestriction_initial] at h
  exact h.symm
end Initial

end FLT.Mazur.WeierstrassDividedDepth
