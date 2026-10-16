/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedRetainedChartIso
public import FLT.Mazur.WeierstrassRetainedFixedNaturality

/-!
# The full retained chart inverses preserve arithmetic restriction

The entire original retained node is isomorphic to the fixed-smoothing node,
and both directions commute with the specified coefficient maps. This is a
whole-chart comparison, before imposing terminal gluing compatibility.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] {W : WeierstrassCurve R} {π : R} {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m k : ℕ) (hk : k ≤ n) (a : Fin k)
local notation "t" => fun i ↦ parameter R π i
local notation "τ" => fun i ↦ arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π i
local notation "q" => fun i ↦ arithmeticStartOneQuotient W H.a1_unit π i
local notation "V" => fun i ↦ arithmeticRetainedFullCorrection data H i k hk a
local notation "C" => fun i ↦ arithmeticRetainedFixedSmoothingIso data H i k hk a
local notation "f" => AlgHom.toRingHom (restriction R π m)
local notation "S" => Spec.map (CommRingCat.ofHom
  (ringMap f (t (m + 1)) (t m) (restriction_parameter R π m)))
local notation "T" => Spec.map (CommRingCat.ofHom
  (ringMap f (τ (m + 1)) (τ m)
    (arithmeticInitialMobiusSmoothing_restriction W H.a1_unit (π ^ 1) π m)))

/-- The whole original retained chart preserves the original arithmetic coefficient map. -/
@[reassoc] theorem arithmeticRetainedFixedSmoothingIso_restriction :
    S ≫ (C (m + 1)).hom = (C m).hom ≫ T := by
  have hu : Units.map (ringMap f (t (m + 1)) (t m)
      (restriction_parameter R π m)).toMonoidHom
      (retainedScaledCorrectionUnit (t (m + 1))
        (retainedDepthScale (q (m + 1)) 1 a.val) (V (m + 1))) =
      retainedScaledCorrectionUnit (t m) (retainedDepthScale (q m) 1 a.val) (V m) := by
    rw [retainedScaledCorrectionUnit_coefficients f _ _ (restriction_parameter R π m)
      (V (m + 1)) (V m) (arithmeticRetainedFullCorrection_restriction data H m k hk a),
      retainedDepthScale_map, map_one, arithmeticStartOneQuotient_restriction]
  exact retainedFixedSmoothingChart_coefficients f (t (m + 1)) (τ (m + 1)) _
    (arithmeticStartOneQuotient_relation W H.a1_unit π (m + 1)) (t m) (τ m) _
    (restriction_parameter R π m)
    (arithmeticInitialMobiusSmoothing_restriction W H.a1_unit (π ^ 1) π m)
    (congrArg Units.val (arithmeticStartOneQuotient_restriction W H.a1_unit π m))
    (arithmeticStartOneQuotient_relation W H.a1_unit π m) _ _ hu

/-- The actual inverse on the complete chart is compatible with the same restrictions. -/
@[reassoc] theorem arithmeticRetainedFixedSmoothingIso_inv_restriction :
    T ≫ (C (m + 1)).inv = (C m).inv ≫ S := by
  apply (cancel_mono (C (m + 1)).hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id,
    Category.assoc, arithmeticRetainedFixedSmoothingIso_restriction,
    ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

end FLT.Mazur.WeierstrassDividedDepth
