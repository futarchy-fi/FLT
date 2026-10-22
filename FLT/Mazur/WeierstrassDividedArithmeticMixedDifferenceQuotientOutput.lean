/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticMixedCoverage
public import FLT.Mazur.WeierstrassDividedArithmeticMixedZeroNodalCoverage

/-!
# The mixed difference formula over the entire arithmetic quotient

Lift the existing retained/terminal smooth output to its original arithmetic
quotient. This includes creation depth zero and preserves all coefficients.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
  globalIntegralAtlasObject globalIntegralAtlasMap globalSmoothAtlasOpen globalSmoothAtlasMap
  retainedOlderLowerCoordinates retainedOlderFormulaIndex terminalLowerCoordinates
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  [IsLocalRing R] {W : WeierstrassCurve R} {π : R} {n depth : ℕ}
  (node : SplitNodeDepth W π depth)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (m j : ℕ) (hj : j ≤ n) (k : ℕ) (hk : k < j)
local notation "hπ" => node.uniformizer_ne_zero
local notation "a" => retainedOlderFormulaIndex j k hk
local notation "b" => (1 : Fin (j + 3))
local notation "d" => data ⟨k, Nat.lt_succ_of_le (hk.le.trans hj)⟩
local notation "e" => data ⟨j, Nat.lt_succ_of_le hj⟩
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "U" => (base).smoothLocus
local notation "t" => (U).ι ≫ base
local notation "Q" => Quotient R π m
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))
local notation "chart" => arithmeticTensorAtlasMap hπ data m j hj
local notation "s" => finiteGlobalArithmeticStructure hπ data j hj m
local notation "O" => tensorIntegralAtlasSmoothOpen hπ data Q j hj
local notation "fa" => (O a).ι ≫ chart a ≫ s
local notation "fb" => (O b).ι ≫ chart b ≫ s
local notation "input" => arithmeticRetainedTerminalFormulaInput hπ data m j hj k j hk le_rfl
local notation "al" => unequalPairLeft d e
local notation "ar" => unequalPairRight d e
local notation "D" => arithmeticRetainedTerminalOpen hπ data m j hj k j hk le_rfl hk.le
local notation "out" => arithmeticRetainedTerminalAddition hπ data m j hj k j hk le_rfl hk.le

/-- The genuine mixed difference output, with its original arithmetic coefficient point. -/
def arithmeticMixedDifferenceQuotientOutput : (D).toScheme ⟶ pullback q t :=
  pullback.lift ((D).ι ≫ pullback.fst fa fb ≫ fa) out (by
    simpa only [Category.assoc] using
      (arithmeticRetainedTerminalAddition_structure
        hπ data m j hj k j hk le_rfl hk.le).symm)

/-- The entire first original coefficient morphism is retained. -/
@[reassoc] theorem arithmeticMixedDifferenceQuotientOutput_base :
    arithmeticMixedDifferenceQuotientOutput node data m j hj k hk ≫ pullback.fst q t =
      (D).ι ≫ pullback.fst fa fb ≫ fa := by
  rw [arithmeticMixedDifferenceQuotientOutput, pullback.lift_fst]

/-- Forgetting the quotient lift recovers the constructed integral smooth output. -/
@[reassoc] theorem arithmeticMixedDifferenceQuotientOutput_integral :
    arithmeticMixedDifferenceQuotientOutput node data m j hj k hk ≫ pullback.snd q t = out := by
  rw [arithmeticMixedDifferenceQuotientOutput, pullback.lift_snd]

end FLT.Mazur.WeierstrassDividedDepth
