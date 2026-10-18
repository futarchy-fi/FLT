/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroInfinityNormalizedRetainedAttachment
public import FLT.Mazur.WeierstrassModificationXArithmeticFactorRatioNilpotence

/-!
# Separation of the two complete retained attachments

Nilpotence of the actual original smoothing separates the left edges of the
independent normalized pair. The complete source comparison reflects this
separation and identifies the entire preimage of either attachment.
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
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "r" => rightBranchOpen Q τ
local notation "r'" => Iso.hom (edgeInversion Q) ≫ r
local notation "v" => arithmeticZeroInfinityNormalizedTargetLeft data H m
local notation "w" => arithmeticZeroInfinityNormalizedRetainedToUnion hπ data H m hj u hu
local notation "F" => arithmeticZeroInfinityNormalizedFullComparison hπ data H m hj u hu

omit [IsDomain R] [IsBezout R] in
/-- The two entire target retained edges are disjoint at every original arithmetic order. -/
theorem arithmeticZeroInfinityNormalizedTargetLeft_disjoint :
    Disjoint (Set.range (v false)) (Set.range (v true)) := by
  apply Set.disjoint_left.mpr
  rintro z ⟨x, hx⟩ ⟨y, hy⟩
  have he : pushout.inl r r' (leftBranchOpen Q τ x) =
      pushout.inr r r' (leftBranchOpen Q τ y) := hx.trans hy.symm
  obtain ⟨o, ho, _⟩ := (SchemeOpenPushout.inl_eq_inr_iff r r' _ _).mp he
  exact Set.disjoint_left.mp (branchOpen_nilpotent_disjoint Q τ
    (arithmeticInitialFactorRatioSmoothing_pow_nilpotent W H.a1_unit π m 1 (by omega)))
    ⟨x, rfl⟩ ⟨o, ho⟩

/-- Either target boundary has exactly its full reparameterized original source edge as preimage. -/
theorem arithmeticZeroInfinityNormalizedRetainedToUnion_preimage (b : Bool) :
    (F).hom ⁻¹' Set.range (v b) = Set.range (w b) := by
  ext z
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x, (F).hom.homeomorph.injective ?_⟩
    change (w b ≫ (F).hom) x = (F).hom z
    rw [arithmeticZeroInfinityNormalizedRetainedToUnion_comparison]
    exact hx
  · rintro ⟨x, rfl⟩
    refine ⟨x, ?_⟩
    exact (congrArg (fun k ↦ k x)
      (arithmeticZeroInfinityNormalizedRetainedToUnion_comparison hπ data H m hj u hu b)).symm

/-- The two actual full retained attachments stay disjoint in the original source union. -/
theorem arithmeticZeroInfinityNormalizedRetainedToUnion_disjoint :
    Disjoint (Set.range (w false)) (Set.range (w true)) := by
  rw [← arithmeticZeroInfinityNormalizedRetainedToUnion_preimage,
    ← arithmeticZeroInfinityNormalizedRetainedToUnion_preimage]
  exact (arithmeticZeroInfinityNormalizedTargetLeft_disjoint data H m).preimage (F).hom

omit [IsDomain R] [IsBezout R] in
/-- Each full target retained boundary preserves the complete original quotient coefficients. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedTargetLeft_base (b : Bool) :
    v b ≫ arithmeticZeroInfinityNormalizedTargetToBase data H m =
      Spec.map (CommRingCat.ofHom (algebraMap Q Q[T;T⁻¹])) := by
  cases b <;>
    simp only [arithmeticZeroInfinityNormalizedTargetLeft, Bool.false_eq_true, ↓reduceIte,
      Category.assoc, arithmeticZeroInfinityNormalizedTargetToBase_first,
      arithmeticZeroInfinityNormalizedTargetToBase_opposite, leftBranchOpen_base]

/-- The full source attachment has the same unreduced coefficient projection. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedRetainedToUnion_base (b : Bool) :
    w b ≫ (arithmeticZeroInfinityNormalizedFullUnion hπ data H m hj u hu).ι ≫
      arithmeticZeroDiagonalSourceToBase hπ data H m hj u hu =
        Spec.map (CommRingCat.ofHom (algebraMap Q Q[T;T⁻¹])) := by
  rw [← arithmeticZeroInfinityNormalizedFullComparison_base,
    arithmeticZeroInfinityNormalizedRetainedToUnion_comparison_assoc,
    arithmeticZeroInfinityNormalizedTargetLeft_base]

end FLT.Mazur.WeierstrassDividedDepth
