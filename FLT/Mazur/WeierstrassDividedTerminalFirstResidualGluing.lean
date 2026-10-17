/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTerminalFirstResidualFactors
public import FLT.Mazur.WeierstrassDividedTerminalChangedAttachment

/-!
# Removing the full first-order residual from both closing spans

Both original changed attachments compare with standard punctures on their
respective smoothing nodes. The same whole terminal isomorphism works on
both branches. The retained corrections fix their opposite punctures.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing LaurentPolynomial WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => PolygonArithmeticStages.Quotient R π 1
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π 1
local notation "σ" => arithmeticTerminalChangedSmoothing data H 1 j hj u hu
local notation "F" => arithmeticFirstResidualTerminalFactor hπ data H j hj u hu
local notation "A" => arithmeticFirstResidualRetainedFactor hπ data H j hj u hu
local notation "K" => arithmeticFirstResidualOverlapFactor hπ data H j hj u hu
local notation "L" => arithmeticClosingRetainedBoundary data H 1
local notation "D" => arithmeticTerminalChangedBoundary data H 1 j hj u hu

/-- The single terminal isomorphism removes both positive residual factors. -/
def arithmeticFirstResidualTerminalIso :
    PolygonSmoothing.chart Q σ ≅ PolygonSmoothing.chart Q σ :=
  (Scheme.Spec.mapIso (F).toRingEquiv.toCommRingCatIso.op).symm

/-- Each original retained node realizes its complementary Laurent correction. -/
def arithmeticFirstResidualRetainedIso (b : Bool) :
    PolygonSmoothing.chart Q τ ≅ PolygonSmoothing.chart Q τ :=
  Scheme.Spec.mapIso (A b).toRingEquiv.toCommRingCatIso.op

/-- The entire overlap is reparametrized by the complementary full Laurent factor. -/
def arithmeticFirstResidualOverlapIso (b : Bool) : branchTorus Q ≅ branchTorus Q :=
  Scheme.Spec.mapIso (K b).toRingEquiv.toCommRingCatIso.op

local notation "FI" => arithmeticFirstResidualTerminalIso hπ data H j hj u hu
local notation "AI" => arithmeticFirstResidualRetainedIso hπ data H j hj u hu
local notation "KI" => arithmeticFirstResidualOverlapIso hπ data H j hj u hu

/-- The retained closing equation keeps its actual reciprocal orientation. -/
@[reassoc] theorem arithmeticFirstResidualRetained_square (b : Bool) :
    L ≫ (AI b).hom = (KI b).hom ≫ L := by
  simp only [arithmeticClosingRetainedBoundary, leftBranchOpen_eq_spec]
  change (Spec.map _ ≫ Spec.map _) ≫ Spec.map _ =
    Spec.map _ ≫ Spec.map _ ≫ Spec.map _
  simp only [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  change invert (leftLaurentMap τ (A b z)) =
    invert (LaurentSquareZeroAutomorphism.subst (parameter R π 1) (parameter_pow R π 1)
      (LaurentBoundaryVectorField.reciprocalField
        (LaurentBoundaryCorrectionSplit.nonpositivePart
          (arithmeticFirstResidualField hπ data H j hj u hu b)))
            (invert (invert (leftLaurentMap τ z))))
  rw [involutive_invert]
  exact congrArg invert (DFunLike.congr_fun (squareZeroReciprocalFactor_left ..) z)

/-- Both full changed terminal boundaries become the standard respective punctures. -/
@[reassoc] theorem arithmeticFirstResidualTerminal_square (b : Bool) :
    D b ≫ (FI).hom = (KI b).hom ≫
      (if b then leftBranchOpen Q σ else rightBranchOpen Q σ) := by
  apply (cancel_mono (FI).inv).mp
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id, Category.assoc]
  rw [arithmeticTerminalChangedBoundary, ← arithmeticTerminalResidualEquiv_spec]
  have hp : (if b then leftBranchOpen Q σ else rightBranchOpen Q σ) =
      Spec.map (CommRingCat.ofHom
        (if b then leftLaurentMap σ else (leftLaurentMap σ).comp (branchSwapMap σ)).toRingHom) := by
    cases b
    · exact rightBranchOpen_eq_spec σ
    · exact leftBranchOpen_eq_spec Q σ
  rw [hp]
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _ ≫ Spec.map _
  simp only [← Spec.map_comp]
  exact congrArg Spec.map (CommRingCat.hom_ext (congrArg AlgHom.toRingHom
    (arithmeticFirstResidual_boundary hπ data H j hj u hu b)))

/-- Both full first-order closing spans have standard punctures after the constructed correction. -/
def arithmeticFirstStandardClosingSpanIso (b : Bool) :
    span L (D b) ≅
      span L (if b then leftBranchOpen Q σ else rightBranchOpen Q σ) :=
  spanIsoMk (KI b) (AI b) FI
    (arithmeticFirstResidualRetained_square hπ data H j hj u hu b)
    (arithmeticFirstResidualTerminal_square hπ data H j hj u hu b)

instance arithmeticFirstStandardClosingBoundary_isOpenImmersion (b : Bool) :
    IsOpenImmersion (if b then leftBranchOpen Q σ else rightBranchOpen Q σ) := by
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> infer_instance

/-- The whole original changed closing attachment has the standard first-order pair gluing. -/
def arithmeticFirstStandardClosingAttachmentIso (b : Bool) :
    arithmeticChangedClosingAttachment data H 1 j hj u hu b ≅
      pushout L (if b then leftBranchOpen Q σ else rightBranchOpen Q σ) :=
  asIso (pushout.map L (D b) L
    (if b then leftBranchOpen Q σ else rightBranchOpen Q σ)
    (AI b).hom (FI).hom (KI b).hom
    (arithmeticFirstResidualRetained_square hπ data H j hj u hu b)
    (arithmeticFirstResidualTerminal_square hπ data H j hj u hu b))

/-- The original full source attachment has the constructed first-order standard pair gluing. -/
def arithmeticFirstOriginalStandardClosingIso (b : Bool) :
    arithmeticOriginalClosingAttachment data H 1 j hj b ≅
      pushout L (if b then leftBranchOpen Q σ else rightBranchOpen Q σ) :=
  arithmeticChangedClosingAttachmentIso data H 1 j hj u hu b ≪≫
    arithmeticFirstStandardClosingAttachmentIso hπ data H j hj u hu b

/-- The retained correction fixes the full opposite puncture in the geometric chart. -/
@[reassoc] theorem arithmeticFirstResidualRetainedIso_opposite (b : Bool) :
    rightBranchOpen Q τ ≫ (AI b).hom = rightBranchOpen Q τ := by
  rw [rightBranchOpen_eq_spec]
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  exact congrArg Spec.map (CommRingCat.hom_ext (congrArg AlgHom.toRingHom
    (arithmeticFirstResidualRetainedFactor_opposite hπ data H j hj u hu b)))

variable [IsBezout R]
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction

/-- The entire original two-label open union has this same standard first-order attachment. -/
def arithmeticFirstOriginalStandardClosingUnionIso (b : Bool) :
    (originalClosingChartUnion hπ data H 1 j hj b).toScheme ≅
      pushout L (if b then leftBranchOpen Q σ else rightBranchOpen Q σ) :=
  arithmeticChangedClosingUnionIso data H 1 j hj u hu hπ b ≪≫
    arithmeticFirstStandardClosingAttachmentIso hπ data H j hj u hu b

end FLT.Mazur.WeierstrassDividedDepth
