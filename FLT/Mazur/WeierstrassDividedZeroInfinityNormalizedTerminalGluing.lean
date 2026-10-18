/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroInfinityNormalizedTerminalBoundary

/-!
# The complete original stage with its common terminal attached

Glue the five-chart comparison across both original closing punctures at once.
The resulting independent exact-twist target is isomorphic to the entire
original stage. Standardizing the retained twists remains a separate problem.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticZeroFiniteAtlasIso simultaneousTwistedArithmeticIso
  arithmeticZeroFiniteInitialIso arithmeticInitialFactorRatioChart
  arithmeticZeroDiagonalAtlasChart
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "c" => arithmeticZeroDiagonalAtlasChart hπ data H m hj u hu
local notation "j" => arithmeticZeroInfinityNormalizedRetainedPairToGlobal hπ data H m hj u hu
local notation "E" => arithmeticZeroInfinityNormalizedRetainedPairIso hπ data H m hj u hu
local notation "J" => arithmeticZeroInfinityNormalizedRetainedPairUnionIso hπ data H m hj u hu
local notation "V" => arithmeticZeroInfinityNormalizedRetainedPairUnion hπ data H m hj u hu
local notation "a" => arithmeticZeroInfinityNormalizedTerminalSource hπ data H m hj u hu
local notation "b" => arithmeticZeroInfinityNormalizedTerminalTarget hπ data H m hj u hu
local notation "r" => arithmeticZeroInfinityNormalizedTerminalSide hπ data H m hj u hu
local notation "X" => simultaneousTwistedArithmeticStage hπ data H m 0 hj u hu

/-- The whole source double attachment and common terminal cover every original point. -/
theorem arithmeticZeroInfinityNormalizedTerminal_source_cover (z : X) :
    (∃ x, j x = z) ∨ ∃ y, c .terminal y = z := by
  rcases arithmeticZeroInfinityNormalizedTerminal_pair_cover hπ data H m hj u hu z with
    ⟨x, rfl⟩ | ht
  · left
    refine ⟨(J).inv x, ?_⟩
    have h : (J).inv ≫ j = (V).ι := by
      rw [← arithmeticZeroInfinityNormalizedRetainedPairUnionIso_global hπ data H m hj u hu,
        Iso.inv_hom_id_assoc]
    exact congrArg (fun f ↦ f x) h
  · exact Or.inr ht

/-- The actual complete stage is the full source pushout across both original closing edges. -/
def arithmeticZeroInfinityNormalizedTerminalSourceIso : pushout a r ≅ X :=
  SchemeOpenPushout.coverIso a r j (c .terminal)
    (arithmeticZeroInfinityNormalizedTerminal_isPullback hπ data H m hj u hu)
    (arithmeticZeroInfinityNormalizedTerminal_source_cover hπ data H m hj u hu)

/-- The full target attaches the one common terminal to both independently retained nodes. -/
def arithmeticZeroInfinityNormalizedGlobalTarget : Scheme := pushout b r

/-- The entire five-chart comparison extends across the whole terminal by the identity. -/
def arithmeticZeroInfinityNormalizedTerminalPushoutIso :
    pushout a r ≅ arithmeticZeroInfinityNormalizedGlobalTarget hπ data H m hj u hu :=
  asIso (pushout.map a r b r (E).hom (𝟙 _) (𝟙 _)
    (by simpa only [Category.id_comp] using
      arithmeticZeroInfinityNormalizedTerminalSource_comparison hπ data H m hj u hu)
    (by simp only [Category.comp_id, Category.id_comp]))

local notation "F" => arithmeticZeroInfinityNormalizedTerminalPushoutIso hπ data H m hj u hu
local notation "I" => arithmeticZeroInfinityNormalizedTerminalSourceIso hπ data H m hj u hu

/-- The complete source presentation retains the exact five-chart global inclusion. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedTerminalSourceIso_pair :
    pushout.inl a r ≫ (I).hom = j := pushout.inl_desc _ _ _

/-- The complete source presentation retains its single original full terminal chart. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedTerminalSourceIso_terminal :
    pushout.inr a r ≫ (I).hom = c .terminal := pushout.inr_desc _ _ _

/-- The full pushout comparison retains the already constructed five-chart comparison. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedTerminalPushoutIso_pair :
    pushout.inl a r ≫ (F).hom = (E).hom ≫ pushout.inl b r := pushout.inl_desc _ _ _

/-- The full pushout comparison is the identity on every point of the common terminal. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedTerminalPushoutIso_terminal :
    pushout.inr a r ≫ (F).hom = pushout.inr b r := by
  change pushout.inr a r ≫ pushout.desc _ _ _ = _
  rw [pushout.inr_desc, Category.id_comp]

/-- The entire original stage compares with the independent target with exact retained twists. -/
def arithmeticZeroInfinityNormalizedGlobalComparison :
    X ≅ arithmeticZeroInfinityNormalizedGlobalTarget hπ data H m hj u hu := (I).symm ≪≫ F

local notation "G" => arithmeticZeroInfinityNormalizedGlobalComparison hπ data H m hj u hu

/-- The global comparison keeps the complete five-chart comparison on its original open image. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedGlobalComparison_pair :
    j ≫ (G).hom = (E).hom ≫ pushout.inl b r := by
  rw [← arithmeticZeroInfinityNormalizedTerminalSourceIso_pair hπ data H m hj u hu]
  simp only [arithmeticZeroInfinityNormalizedGlobalComparison, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.hom_inv_id_assoc,
    arithmeticZeroInfinityNormalizedTerminalPushoutIso_pair]

/-- The global comparison keeps the entire original common terminal without any correction. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedGlobalComparison_terminal :
    c .terminal ≫ (G).hom = pushout.inr b r := by
  rw [← arithmeticZeroInfinityNormalizedTerminalSourceIso_terminal hπ data H m hj u hu]
  simp only [arithmeticZeroInfinityNormalizedGlobalComparison, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.hom_inv_id_assoc,
    arithmeticZeroInfinityNormalizedTerminalPushoutIso_terminal]

end FLT.Mazur.WeierstrassDividedDepth
