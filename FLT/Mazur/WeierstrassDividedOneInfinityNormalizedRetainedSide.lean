/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOneInfinityNormalizedRetainedAttachment
public import FLT.Mazur.WeierstrassDividedZeroInfinityNormalizedRetainedSide

/-!
# The exact full retained-node side of the normalized attachment

Keep the entire K inverse and original base substitution. The exact attachment
enters the whole retained node 0 on each arm, preserving its full branch image.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticOneFiniteInitialIso arithmeticInitialFactorRatioChart arithmeticOneFiniteAtlasIso
  arithmeticOneDiagonalAtlasChart simultaneousTwistedArithmeticRestriction
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 2 ≤ n)
  (u : Rˣ) (hu : (data ⟨2, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => fun k ↦ Quotient R π k
local notation "D" => arithmeticOneDiagonalState hπ data H hj u hu
local notation "s" => fun m b ↦ PolygonArithmeticRetainedChain.State.retained D m 0 b
local notation "K" => fun k ↦
  arithmeticOneInfinityNormalizedRetainedParameter hπ data H k hj u hu
local notation "U" => fun k ↦ arithmeticOneInfinityNormalizedFullUnion hπ data H k hj u hu
local notation "w" => fun k ↦
  arithmeticOneInfinityNormalizedRetainedToUnion hπ data H k hj u hu
local notation "c" => fun k ↦ arithmeticOneDiagonalAtlasChart hπ data H k hj u hu
/-- The exact retained-side boundary in the entire original corrected retained node. -/
def arithmeticOneInfinityNormalizedRetainedSide (b : Bool) :
    branchTorus (Q m) ⟶ PolygonSmoothing.chart (Q m) (s m b) :=
  (K m b).inv ≫ (punctureSpecIso (arithmeticInitialBaseEquiv data H m 1 hj)).hom ≫
    rightBranchOpen (Q m) (s m b)

local notation "r" => fun k ↦ arithmeticOneInfinityNormalizedRetainedSide hπ data H k hj u hu

instance arithmeticOneInfinityNormalizedRetainedSide_isOpenImmersion (b : Bool) :
    IsOpenImmersion (r m b) := by
  unfold arithmeticOneInfinityNormalizedRetainedSide
  infer_instance

/-- The exact retained-side substitution agrees with the full original source attachment. -/
@[reassoc] theorem arithmeticOneInfinityNormalizedRetainedSide_global (b : Bool) :
    r m b ≫ c m (.retained ⟨0, by omega⟩ b) = w m b ≫ (U m).ι := by
  simpa only [arithmeticOneInfinityNormalizedRetainedSide, Category.assoc] using
    (arithmeticOneInfinityNormalizedRetainedToUnion_global hπ data H m hj u hu b).symm

omit [IsBezout R] in
/-- The exact boundary parameter changes no point of the full right-branch image. -/
theorem arithmeticOneInfinityNormalizedRetainedSide_range (b : Bool) :
    Set.range (r m b) = Set.range (rightBranchOpen (Q m) (s m b)) :=
  fullChart_twoIso_comp_range (K m b).symm
    (punctureSpecIso (arithmeticInitialBaseEquiv data H m 1 hj)) _

end FLT.Mazur.WeierstrassDividedDepth
