/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedRetainedChartIso
public import FLT.Mazur.WeierstrassRetainedFixedTerminalEdges

/-!
# The original retained maps are open immersions into the fixed polygon

Whole-chart invertibility upgrades the constructed retained comparison to
an open immersion at every original label. The original adjacent, first-edge
and closing-edge equations still refer to these same maps.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m k : ℕ) (hk : k ≤ n)
local notation "Q" => Quotient R π m
local notation "t" => parameter R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "hn" => Fact.mk
  (arithmeticInitialFactorRatioSmoothing_nilpotent W H.a1_unit (π ^ 1) π m H.scale_div)

omit [IsBezout R] in
/-- The actual retained comparison is a full chart isomorphism followed by its polygon label. -/
theorem arithmeticStartOneRetainedMap_factorization (a : Fin k) (b : Bool) :
    let _ := hn
    arithmeticStartOneRetainedMap hπ data H m k hk a b =
      (arithmeticRetainedFixedSmoothingIso data H m k hk a).hom ≫
        retainedPolygonMap Q τ k a b := rfl

/-- Both original retained atlas labels embed openly into the same normalized polygon. -/
instance arithmeticStartOneRetainedMap_isOpenImmersion (a : Fin k) (b : Bool) :
    IsOpenImmersion (arithmeticStartOneRetainedMap hπ data H m k hk a b) := by
  let _ := hn
  rw [arithmeticStartOneRetainedMap_factorization]
  exact IsOpenImmersion.comp _ _

/-- The first original full factor-ratio map is therefore an open immersion as well. -/
instance arithmeticFactorRatioFirstRetainedMap_isOpenImmersion (hk0 : 0 < k) (b : Bool) :
    IsOpenImmersion (arithmeticFactorRatioFirstRetainedMap hπ data H m k hk hk0 b) := by
  rw [← arithmeticStartOneRetainedMap_first hπ data H m k hk hk0 b]
  infer_instance

end FLT.Mazur.WeierstrassDividedDepth
