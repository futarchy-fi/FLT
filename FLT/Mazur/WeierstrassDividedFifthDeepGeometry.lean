/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFifthDeepEndCancellation
public import FLT.Mazur.WeierstrassDividedFifthShallowTransitions
public import FLT.Mazur.PolygonArithmeticHigherPunctureIdentification

/-!
# Geometry of the fifth outer retained chain

All three paired factors and the next earlier factor are whole-node isomorphisms.
Their outgoing and reciprocal incoming punctures keep the exact input smoothings.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
  (m : ℕ)
local notation "Q" => Quotient R π m
local notation "s" => fun v ↦ arithmeticFifthDeepInput hπ data H j hj u hu v m
local notation "t" => fun v ↦ arithmeticFifthDeepSmoothing hπ data H j hj u hu v m
local notation "P" => fun v ↦ arithmeticFifthPairedIntegralField hπ data H j hj u hu
  (fifthDeepOutgoing v) (fifthDeepIncoming v)

/-- Each paired fifth node changes from its actual fourth smoothing to its full fifth one. -/
def arithmeticFifthDeepNodeIso (v : FifthDeepNode) (b : Bool) :
    PolygonSmoothing.chart Q (s v b) ≅ PolygonSmoothing.chart Q (t v b) :=
  Scheme.Spec.mapIso
    (arithmeticFifthDeepFactor hπ data H j hj u hu v m b).toRingEquiv.toCommRingCatIso.op

local notation "N" => arithmeticFifthDeepNodeIso hπ data H j hj u hu m

/-- Both full punctures are supplied by the same geometric node isomorphism. -/
@[reassoc] theorem arithmeticFifthDeepNodeIso_puncture (v : FifthDeepNode) (b a : Bool) :
    punctureOpen (s v b) a ≫ (N v b).hom =
      (punctureSpecIso (twoBranchCorrectionPunctureFactor R π m (s v b) (P v b) a)).hom ≫
        punctureOpen (t v b) a := by
  apply punctureFactor_spec
  exact arithmeticFifthDeepFactor_puncture hπ data H j hj u hu v m b a

/-- The complete reciprocal incoming substitution at any of the three retained nodes. -/
def arithmeticFifthDeepEdgeIso (v : FifthDeepNode) (b : Bool) : branchTorus Q ≅ branchTorus Q :=
  edgeInversion Q ≪≫
    punctureSpecIso (twoBranchCorrectionPunctureFactor R π m (s v b) (P v b) false) ≪≫
      (edgeInversion Q).symm

local notation "K" => arithmeticFifthDeepEdgeIso hπ data H j hj u hu m

/-- The incoming puncture keeps the exact fourth and fifth smoothing in its geometric square. -/
@[reassoc] theorem arithmeticFifthDeepNodeIso_incoming (v : FifthDeepNode) (b : Bool) :
    precedingBranch Q (s v b) ≫ (N v b).hom = (K v b).hom ≫ precedingBranch Q (t v b) := by
  have h := arithmeticFifthDeepNodeIso_puncture hπ data H j hj u hu m v b false
  simp only [punctureOpen_false] at h
  simp only [arithmeticFifthDeepEdgeIso, Iso.trans_hom, Iso.symm_hom,
    precedingBranch, Category.assoc, Iso.inv_hom_id_assoc]
  rw [h]

/-- The full algebraic reciprocal substitution realizes the geometric incoming correction. -/
theorem arithmeticFifthDeepEdgeEquiv_spec (v : FifthDeepNode) (b : Bool) :
    punctureSpecIso (arithmeticFifthPairedEdgeEquiv hπ data H j hj u hu
      (fifthDeepOutgoing v) (fifthDeepIncoming v) m (s v b) b) = K v b := by
  simp only [arithmeticFifthPairedEdgeEquiv, punctureSpecIso_trans,
    punctureSpecIso_invert, arithmeticFifthDeepEdgeIso]
  rfl

local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "A" => arithmeticFifthDeepEarlierIntegralField hπ data H j hj u hu
local notation "e" => arithmeticFifthDeepEarlierSmoothing hπ data H j hj u hu m

/-- The next earlier normalized node also retains its complete fifth correction. -/
def arithmeticFifthDeepEarlierIso (b : Bool) :
    PolygonSmoothing.chart Q τ ≅ PolygonSmoothing.chart Q (e b) :=
  Scheme.Spec.mapIso
    (arithmeticFifthDeepEarlierFactor hπ data H j hj u hu m b).toRingEquiv.toCommRingCatIso.op

/-- Both earlier punctures retain their full geometric square. -/
@[reassoc] theorem arithmeticFifthDeepEarlierIso_puncture (b a : Bool) :
    punctureOpen τ a ≫ (arithmeticFifthDeepEarlierIso hπ data H j hj u hu m b).hom =
      (punctureSpecIso (correctionPunctureFactor R π m τ (A b) a)).hom ≫ punctureOpen (e b) a := by
  apply punctureFactor_spec
  exact arithmeticFifthDeepEarlierFactor_puncture hπ data H j hj u hu m b a

end FLT.Mazur.WeierstrassDividedDepth
