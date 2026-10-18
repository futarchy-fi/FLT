/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroInfinityNormalizedRetainedRestriction

/-!
# The exact full retained-node side of the normalized attachment

Keep the entire K inverse and original base substitution. This open boundary
has the original coefficient square and base, and its full node is unchanged.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticZeroFiniteInitialIso arithmeticInitialFactorRatioChart arithmeticZeroFiniteAtlasIso
  arithmeticZeroDiagonalAtlasChart simultaneousTwistedArithmeticRestriction
/-- Two full parameter isomorphisms preserve the image of a chart map. -/
theorem fullChart_twoIso_comp_range {A B C X : Scheme}
    (e : A ≅ B) (d : B ≅ C) (f : C ⟶ X) :
    Set.range (e.hom ≫ d.hom ≫ f) = Set.range f :=
  (d.hom.homeomorph.surjective.comp e.hom.homeomorph.surjective).range_comp f

variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => fun k ↦ Quotient R π k
local notation "D" => arithmeticZeroDiagonalState hπ data H 0 hj u hu
local notation "s" => PolygonArithmeticSimultaneous.State.last D
local notation "K" => fun k ↦
  arithmeticZeroInfinityNormalizedRetainedParameter hπ data H k hj u hu
local notation "U" => fun k ↦ arithmeticZeroInfinityNormalizedFullUnion hπ data H k hj u hu
local notation "w" => fun k ↦
  arithmeticZeroInfinityNormalizedRetainedToUnion hπ data H k hj u hu
local notation "c" => fun k ↦ arithmeticZeroDiagonalAtlasChart hπ data H k hj u hu
local notation "S" => arithmeticZeroDiagonalAtlasRestriction hπ data H hj u hu m
local notation "q" => simultaneousTwistedArithmeticRestriction hπ data H m 0 hj u hu
local notation "ρ" => closingOverlapRestriction (R := R) (π := π) m

/-- The exact retained-side boundary in the entire original corrected retained node. -/
def arithmeticZeroInfinityNormalizedRetainedSide (b : Bool) :
    branchTorus (Q m) ⟶ PolygonSmoothing.chart (Q m) (s m b) :=
  (K m b).inv ≫ (punctureSpecIso (arithmeticInitialBaseEquiv data H m 0 hj)).hom ≫
    rightBranchOpen (Q m) (s m b)

local notation "r" => fun k ↦ arithmeticZeroInfinityNormalizedRetainedSide hπ data H k hj u hu

instance arithmeticZeroInfinityNormalizedRetainedSide_isOpenImmersion (b : Bool) :
    IsOpenImmersion (r m b) := by
  unfold arithmeticZeroInfinityNormalizedRetainedSide
  infer_instance

/-- The exact retained-side substitution agrees with the full original source attachment. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedRetainedSide_global (b : Bool) :
    r m b ≫ c m (.retained ⟨0, by omega⟩ b) = w m b ≫ (U m).ι := by
  simpa only [arithmeticZeroInfinityNormalizedRetainedSide, Category.assoc] using
    (arithmeticZeroInfinityNormalizedRetainedToUnion_global hπ data H m hj u hu b).symm

/-- The full retained-side parameter follows the actual corrected whole-node quotient. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedRetainedSide_restriction (b : Bool) :
    r m b ≫ S (.retained ⟨0, by omega⟩ b) = ρ ≫ r (m + 1) b := by
  apply (cancel_mono (c (m + 1) (.retained ⟨0, by omega⟩ b))).mp
  rw [Category.assoc, arithmeticZeroDiagonalAtlasChart_restriction,
    arithmeticZeroInfinityNormalizedRetainedSide_global_assoc, Category.assoc,
    arithmeticZeroInfinityNormalizedRetainedSide_global,
    ← arithmeticZeroInfinityNormalizedFullUnionRestriction_global,
    ← Category.assoc, arithmeticZeroInfinityNormalizedRetainedToUnion_restriction,
    Category.assoc]

/-- The original retained node boundary is over the full unreduced coefficient ring. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedRetainedSide_base (b : Bool) :
    r m b ≫ chartStructure (Q m) (s m b) =
      Spec.map (CommRingCat.ofHom (algebraMap (Q m) (Q m)[T;T⁻¹])) := by
  rw [← arithmeticZeroDiagonalAtlas_retained_base hπ data H m hj u hu b,
    arithmeticZeroInfinityNormalizedRetainedSide_global_assoc,
    arithmeticZeroInfinityNormalizedRetainedToUnion_base]

omit [IsBezout R] in
/-- The exact boundary parameter changes no point of the full right-branch image. -/
theorem arithmeticZeroInfinityNormalizedRetainedSide_range (b : Bool) :
    Set.range (r m b) = Set.range (rightBranchOpen (Q m) (s m b)) :=
  fullChart_twoIso_comp_range (K m b).symm
    (punctureSpecIso (arithmeticInitialBaseEquiv data H m 0 hj)) _

end FLT.Mazur.WeierstrassDividedDepth
