/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroInitialTotalBase

/-!
# Coefficient bases of the full depth-zero closing corrections

Both last-node factors and inverse common-terminal factors preserve the
original quotient base at every correction round and every arithmetic order.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticZeroFiniteInitialIso arithmeticInitialFactorRatioChart
/-- The inverse of a full node algebra isomorphism also preserves its coefficient base. -/
@[reassoc] theorem nodeAlgebraIso_inv_structure {K : Type} [CommRing K] {s t : K}
    (e : ChartRing t ≃ₐ[K] ChartRing s) :
    (Scheme.Spec.mapIso e.toRingEquiv.toCommRingCatIso.op).inv ≫
      PolygonSmoothing.chartStructure K s = PolygonSmoothing.chartStructure K t := by
  apply (cancel_epi (Scheme.Spec.mapIso e.toRingEquiv.toCommRingCatIso.op).hom).mp
  rw [Iso.hom_inv_id_assoc, nodeAlgebraIso_structure]

variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m

/-- The first whole last-node factor preserves its full coefficient base. -/
@[reassoc] theorem arithmeticZeroFirstLastIso_base (b : Bool) :
    (arithmeticZeroFirstLastIso hπ data H m j hj u hu b).hom ≫
      chartStructure Q (arithmeticZeroFirstLastSmoothing hπ data H j hj u hu m b) =
      chartStructure Q τ :=
  nodeAlgebraIso_structure _

/-- The second whole last-node factor preserves its full coefficient base. -/
@[reassoc] theorem arithmeticZeroSecondLastIso_base (b : Bool) :
    (arithmeticZeroSecondLastIso hπ data H m j hj u hu b).hom ≫
      chartStructure Q (arithmeticZeroSecondLastSmoothing hπ data H j hj u hu m b) =
      chartStructure Q (arithmeticZeroFirstLastSmoothing hπ data H j hj u hu m b) :=
  nodeAlgebraIso_structure _

/-- The second inverse common-terminal factor preserves its full coefficient base. -/
@[reassoc] theorem arithmeticZeroSecondTerminalIso_base :
    (arithmeticZeroSecondTerminalIso hπ data H m j hj u hu).hom ≫
      chartStructure Q (arithmeticZeroSecondTerminalSmoothing hπ data H j hj u hu m) =
      chartStructure Q (arithmeticFourthTerminalSmoothing hπ data H j hj u hu m) :=
  nodeAlgebraIso_inv_structure _

/-- The third whole last-node factor preserves its full coefficient base. -/
@[reassoc] theorem arithmeticZeroThirdLastIso_base (b : Bool) :
    (arithmeticZeroThirdLastIso hπ data H m j hj u hu b).hom ≫
      chartStructure Q (arithmeticZeroThirdLastSmoothing hπ data H j hj u hu m b) =
      chartStructure Q (arithmeticZeroSecondLastSmoothing hπ data H j hj u hu m b) :=
  nodeAlgebraIso_structure _

/-- The third inverse common-terminal factor preserves its full coefficient base. -/
@[reassoc] theorem arithmeticZeroThirdTerminalIso_base :
    (arithmeticZeroThirdTerminalIso hπ data H m j hj u hu).hom ≫
      chartStructure Q (arithmeticZeroThirdTerminalSmoothing hπ data H j hj u hu m) =
      chartStructure Q (arithmeticZeroSecondTerminalSmoothing hπ data H j hj u hu m) :=
  nodeAlgebraIso_inv_structure _

/-- The fourth whole last-node factor preserves its full coefficient base. -/
@[reassoc] theorem arithmeticZeroFourthLastIso_base (b : Bool) :
    (arithmeticZeroFourthLastIso hπ data H m j hj u hu b).hom ≫
      chartStructure Q (arithmeticZeroFourthLastSmoothing hπ data H j hj u hu m b) =
      chartStructure Q (arithmeticZeroThirdLastSmoothing hπ data H j hj u hu m b) :=
  nodeAlgebraIso_structure _

/-- The fourth inverse common-terminal factor preserves its full coefficient base. -/
@[reassoc] theorem arithmeticZeroFourthTerminalIso_base :
    (arithmeticZeroFourthTerminalIso hπ data H m j hj u hu).hom ≫
      chartStructure Q (arithmeticZeroFourthTerminalSmoothing hπ data H j hj u hu m) =
      chartStructure Q (arithmeticZeroThirdTerminalSmoothing hπ data H j hj u hu m) :=
  nodeAlgebraIso_inv_structure _

/-- The fifth whole last-node factor preserves its full coefficient base. -/
@[reassoc] theorem arithmeticZeroFifthLastIso_base (b : Bool) :
    (arithmeticZeroFifthLastIso hπ data H m j hj u hu b).hom ≫
      chartStructure Q (arithmeticZeroFifthLastSmoothing hπ data H j hj u hu m b) =
      chartStructure Q (arithmeticZeroFourthLastSmoothing hπ data H j hj u hu m b) :=
  nodeAlgebraIso_structure _

/-- The fifth inverse common-terminal factor preserves its full coefficient base. -/
@[reassoc] theorem arithmeticZeroFifthTerminalIso_base :
    (arithmeticZeroFifthTerminalIso hπ data H m j hj u hu).hom ≫
      chartStructure Q (arithmeticZeroFifthTerminalSmoothing hπ data H j hj u hu m) =
      chartStructure Q (arithmeticZeroFourthTerminalSmoothing hπ data H j hj u hu m) :=
  nodeAlgebraIso_inv_structure _

/-- The finite whole last-node factor preserves its full coefficient base. -/
@[reassoc] theorem arithmeticZeroFiniteLastIso_base (k : ℕ) (b : Bool) :
    (arithmeticZeroFiniteLastIso hπ data H k m j hj u hu b).hom ≫
      chartStructure Q ((arithmeticZeroFiniteState hπ data H j hj u hu k).last m b) =
      chartStructure Q (arithmeticZeroFifthLastSmoothing hπ data H j hj u hu m b) :=
  nodeAlgebraIso_structure _

/-- The finite inverse common-terminal factor preserves its full coefficient base. -/
@[reassoc] theorem arithmeticZeroFiniteTerminalIso_base (k : ℕ) :
    (arithmeticZeroFiniteTerminalIso hπ data H k m j hj u hu).hom ≫
      chartStructure Q ((arithmeticZeroFiniteState hπ data H j hj u hu k).terminal m) =
      chartStructure Q (arithmeticZeroFifthTerminalSmoothing hπ data H j hj u hu m) :=
  nodeAlgebraIso_inv_structure _

end FLT.Mazur.WeierstrassDividedDepth
