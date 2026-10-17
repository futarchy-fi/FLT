/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFourthOuterRestriction
public import FLT.Mazur.WeierstrassDividedThirdNodeRestriction

/-!
# Full geometric factors and quotient squares for the further retained edge

Each restriction is the actual coefficient map on the stated old or new
smoothing. Both factors retain their actual source and target smoothings.
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
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "s₃" => arithmeticThirdEarlierSmoothing hπ data H j hj u hu m

/-- The earlier node receives both fourth factors from its complete third smoothing. -/
def arithmeticFourthOuterIso (b : Bool) :
    PolygonSmoothing.chart Q (s₃ b) ≅
      PolygonSmoothing.chart Q (arithmeticFourthOuterSmoothing hπ data H j hj u hu m b) :=
  Scheme.Spec.mapIso
    (arithmeticFourthOuterFactor hπ data H j hj u hu m b).toRingEquiv.toCommRingCatIso.op

/-- The farther retained node receives its full positive factor from the normalized source. -/
def arithmeticFourthFartherIso (b : Bool) :
    PolygonSmoothing.chart Q τ ≅
      PolygonSmoothing.chart Q (arithmeticFourthFartherSmoothing hπ data H j hj u hu m b) :=
  Scheme.Spec.mapIso
    (arithmeticFourthFartherFactor hπ data H j hj u hu m b).toRingEquiv.toCommRingCatIso.op

/-- Both earlier punctures come from the simultaneous whole-node comparison. -/
@[reassoc] theorem arithmeticFourthOuterIso_puncture (b a : Bool) :
    punctureOpen (s₃ b) a ≫ (arithmeticFourthOuterIso hπ data H j hj u hu m b).hom =
      (punctureSpecIso (twoBranchCorrectionPunctureFactor R π m (s₃ b)
        (arithmeticFourthOuterIntegralField hπ data H j hj u hu b) a)).hom ≫
          punctureOpen (arithmeticFourthOuterSmoothing hπ data H j hj u hu m b) a := by
  apply punctureFactor_spec
  exact arithmeticFourthOuterFactor_puncture hπ data H j hj u hu m b a

/-- Both farther punctures retain the complete positive factor and its opposite compensation. -/
@[reassoc] theorem arithmeticFourthFartherIso_puncture (b a : Bool) :
    punctureOpen τ a ≫ (arithmeticFourthFartherIso hπ data H j hj u hu m b).hom =
      (punctureSpecIso (correctionPunctureFactor R π m τ
        (arithmeticFourthFartherIntegralField hπ data H j hj u hu b) a)).hom ≫
          punctureOpen (arithmeticFourthFartherSmoothing hπ data H j hj u hu m b) a := by
  apply punctureFactor_spec
  exact arithmeticFourthFartherFactor_puncture hπ data H j hj u hu m b a

local notation "P" => fun k ↦ arithmeticFourthOuterIso hπ data H j hj u hu k
local notation "E" => fun k ↦ arithmeticFourthFartherIso hπ data H j hj u hu k
local notation "s" => arithmeticFourthOuterSmoothing hπ data H j hj u hu
local notation "t" => arithmeticFourthFartherSmoothing hπ data H j hj u hu

/-- The earlier node's explicit coefficient restriction after both new fields. -/
def arithmeticFourthOuterRestriction (b : Bool) :
    PolygonSmoothing.chart (Quotient R π m) (s m b) ⟶
      PolygonSmoothing.chart (Quotient R π (m + 1)) (s (m + 1) b) :=
  Spec.map (CommRingCat.ofHom (ringMap (restriction R π m).toRingHom _ _
    (arithmeticFourthOuterSmoothing_restriction hπ data H j hj u hu m b)))

/-- The farther node's new scalar drift is retained by its explicit quotient. -/
def arithmeticFourthFartherRestriction (b : Bool) :
    PolygonSmoothing.chart (Quotient R π m) (t m b) ⟶
      PolygonSmoothing.chart (Quotient R π (m + 1)) (t (m + 1) b) :=
  Spec.map (CommRingCat.ofHom (ringMap (restriction R π m).toRingHom _ _
    (arithmeticFourthFartherSmoothing_restriction hπ data H j hj u hu m b)))

/-- Both old and new earlier smoothings occur in the actual factor square. -/
@[reassoc] theorem arithmeticFourthOuterIso_restriction (b : Bool) :
    arithmeticThirdEarlierRestriction hπ data H j hj u hu m b ≫ (P (m + 1) b).hom =
      (P m b).hom ≫ arithmeticFourthOuterRestriction hπ data H j hj u hu m b := by
  exact nodeFactorIso_restriction _ _ _ _ _ _ _ _ _
    (arithmeticFourthOuterFactor_restriction hπ data H j hj u hu m b)

/-- The farther full factor keeps the coefficient square on its normalized source smoothing. -/
@[reassoc] theorem arithmeticFourthFartherIso_restriction (b : Bool) :
    closingNormalizedRestriction data H m ≫ (E (m + 1) b).hom =
      (E m b).hom ≫ arithmeticFourthFartherRestriction hπ data H j hj u hu m b := by
  exact nodeFactorIso_restriction _ _ _ _ _ _ _ _ _
    (arithmeticFourthFartherFactor_restriction hπ data H j hj u hu m b)

end FLT.Mazur.WeierstrassDividedDepth
