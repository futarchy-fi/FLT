/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroClosingFactorBase
public import FLT.Mazur.WeierstrassDividedRevisedCorrectionBase

/-!
# Original coefficient bases of the four pre-diagonal closing rounds

The normalized whole-node factors and their original label orientations keep
all quotient coefficients, as do the four common-terminal substitutions.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticZeroFiniteInitialIso arithmeticInitialFactorRatioChart
/-- Identifying equal smoothing parameters preserves the whole node's coefficient map. -/
@[reassoc] theorem nodeParameterIso_structure {K : Type} [CommRing K] (s t : K)
    (h : s = t) : (nodeParameterIso s t h).hom ≫ chartStructure K t =
      chartStructure K s := by
  subst t
  rfl

/-- Conjugating an isomorphism over a base by another one keeps the same base. -/
theorem conjugateIso_structure {X S : Scheme} (p : X ⟶ S) (e f : X ≅ X)
    (he : e.hom ≫ p = p) (hf : f.hom ≫ p = p) :
    (e.symm ≪≫ f ≪≫ e).hom ≫ p = p := by
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, he, hf]
  calc
    e.inv ≫ p = e.inv ≫ e.hom ≫ p := congrArg (e.inv ≫ ·) he.symm
    _ = p := e.inv_hom_id_assoc p

variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m

/-- The complete ResidualLiftRetained factor preserves its original quotient scalars. -/
@[reassoc] theorem arithmeticResidualLiftRetainedIso_base (b : Bool) :
    (arithmeticResidualLiftRetainedIso hπ data H m j hj u hu b).hom ≫
      chartStructure Q τ = chartStructure Q τ := by
  simp only [arithmeticResidualLiftRetainedIso, Iso.trans_hom, Category.assoc,
    nodeParameterIso_structure]
  exact nodeAlgebraIso_structure _

/-- The complete SecondJointRetained factor preserves its original quotient scalars. -/
@[reassoc] theorem arithmeticSecondJointRetainedIso_base (b : Bool) :
    (arithmeticSecondJointRetainedIso hπ data H m j hj u hu b).hom ≫
      chartStructure Q τ = chartStructure Q τ := by
  simp only [arithmeticSecondJointRetainedIso, Iso.trans_hom, Category.assoc,
    nodeParameterIso_structure]
  exact nodeAlgebraIso_structure _

/-- The complete ThirdLast factor preserves its original quotient scalars. -/
@[reassoc] theorem arithmeticThirdLastIso_base (b : Bool) :
    (arithmeticThirdLastIso hπ data H m j hj u hu b).hom ≫
      chartStructure Q τ = chartStructure Q τ := by
  simp only [arithmeticThirdLastIso, Iso.trans_hom, Category.assoc,
    nodeParameterIso_structure]
  exact nodeAlgebraIso_structure _

/-- The complete FourthLast factor preserves its original quotient scalars. -/
@[reassoc] theorem arithmeticFourthLastIso_base (b : Bool) :
    (arithmeticFourthLastIso hπ data H m j hj u hu b).hom ≫
      chartStructure Q τ = chartStructure Q τ := by
  simp only [arithmeticFourthLastIso, Iso.trans_hom, Category.assoc,
    nodeParameterIso_structure]
  exact nodeAlgebraIso_structure _

/-- The original labeled ResidualLift orientation preserves the full coefficient base. -/
@[reassoc] theorem arithmeticResidualLiftOrientedIso_base (b : Bool) :
    (arithmeticResidualLiftOrientedIso hπ data H m j hj u hu b).hom ≫
      chartStructure Q τ = chartStructure Q τ :=
  conjugateIso_structure _ _ _ (twistedRetainedOrientation_base data H m b)
    (arithmeticResidualLiftRetainedIso_base hπ data H m j hj u hu b)

/-- The original labeled SecondJoint orientation preserves the full coefficient base. -/
@[reassoc] theorem arithmeticSecondJointOrientedIso_base (b : Bool) :
    (arithmeticSecondJointOrientedIso hπ data H m j hj u hu b).hom ≫
      chartStructure Q τ = chartStructure Q τ :=
  conjugateIso_structure _ _ _ (twistedRetainedOrientation_base data H m b)
    (arithmeticSecondJointRetainedIso_base hπ data H m j hj u hu b)

/-- The original labeled ThirdLast orientation preserves the full coefficient base. -/
@[reassoc] theorem arithmeticThirdLastOrientedIso_base (b : Bool) :
    (arithmeticThirdLastOrientedIso hπ data H m j hj u hu b).hom ≫
      chartStructure Q τ = chartStructure Q τ :=
  conjugateIso_structure _ _ _ (twistedRetainedOrientation_base data H m b)
    (arithmeticThirdLastIso_base hπ data H m j hj u hu b)

/-- The original labeled FourthLast orientation preserves the full coefficient base. -/
@[reassoc] theorem arithmeticFourthLastOrientedIso_base (b : Bool) :
    (arithmeticFourthLastOrientedIso hπ data H m j hj u hu b).hom ≫
      chartStructure Q τ = chartStructure Q τ :=
  conjugateIso_structure _ _ _ (twistedRetainedOrientation_base data H m b)
    (arithmeticFourthLastIso_base hπ data H m j hj u hu b)

/-- The complete ResidualLiftTerminal inverse factor preserves its full coefficient base. -/
@[reassoc] theorem arithmeticResidualLiftTerminalIso_base :
    (arithmeticResidualLiftTerminalIso hπ data H m j hj u hu).hom ≫
      chartStructure Q (arithmeticResidualLiftTerminalSmoothing hπ data H m j hj u hu) =
      chartStructure Q (arithmeticTerminalChangedSmoothing data H m j hj u hu) :=
  nodeAlgebraIso_inv_structure _

/-- The complete SecondResidualLiftTerminal inverse factor preserves its full coefficient base. -/
@[reassoc] theorem arithmeticSecondResidualLiftTerminalIso_base :
    (arithmeticSecondResidualLiftTerminalIso hπ data H m j hj u hu).hom ≫
      chartStructure Q (arithmeticSecondResidualLiftSmoothing hπ data H j hj u hu m) =
      chartStructure Q (arithmeticResidualLiftTerminalSmoothing hπ data H m j hj u hu) :=
  nodeAlgebraIso_inv_structure _

/-- The complete ThirdTerminal inverse factor preserves its full coefficient base. -/
@[reassoc] theorem arithmeticThirdTerminalIso_base :
    (arithmeticThirdTerminalIso hπ data H m j hj u hu).hom ≫
      chartStructure Q (arithmeticThirdTerminalSmoothing hπ data H j hj u hu m) =
      chartStructure Q (arithmeticSecondResidualLiftSmoothing hπ data H j hj u hu m) :=
  nodeAlgebraIso_inv_structure _

/-- The complete FourthTerminal inverse factor preserves its full coefficient base. -/
@[reassoc] theorem arithmeticFourthTerminalIso_base :
    (arithmeticFourthTerminalIso hπ data H m j hj u hu).hom ≫
      chartStructure Q (arithmeticFourthTerminalSmoothing hπ data H j hj u hu m) =
      chartStructure Q (arithmeticThirdTerminalSmoothing hπ data H j hj u hu m) :=
  nodeAlgebraIso_inv_structure _

/-- All four accumulated last factors keep the whole original arithmetic base. -/
@[reassoc] theorem arithmeticFourthAccumulatedLastIso_base (b : Bool) :
    (arithmeticFourthAccumulatedLastIso hπ data H m j hj u hu b).hom ≫
      chartStructure Q τ = chartStructure Q τ := by
  simp only [arithmeticFourthAccumulatedLastIso, Iso.trans_hom, Category.assoc,
    arithmeticFourthLastOrientedIso_base, arithmeticThirdLastOrientedIso_base,
    arithmeticSecondJointOrientedIso_base, arithmeticResidualLiftOrientedIso_base]

end FLT.Mazur.WeierstrassDividedDepth
