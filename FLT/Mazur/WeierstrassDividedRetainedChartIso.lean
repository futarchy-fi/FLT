/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassRetainedFixedSmoothingIso
public import FLT.Mazur.WeierstrassDividedRetainedClosingIso

/-!
# Constructed inverses of every actual retained fixed-smoothing chart

The original root correction reduces to one in the coefficient ideal.
This supplies whole-chart isomorphisms for the start-one family at every
depth and arithmetic order, with the original depth recurrence intact.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] {W : WeierstrassCurve R} {π : R} {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m k : ℕ) (hk : k ≤ n) (a : Fin k)
local notation "Q" => Quotient R π m
local notation "t" => parameter R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "q" => arithmeticStartOneQuotient W H.a1_unit π m
local notation "hq" => arithmeticStartOneQuotient_relation W H.a1_unit π m
local notation "α" => retainedDepthScale q 1 a.val
local notation "V" => arithmeticRetainedFullCorrection data H m k hk a
local notation "J" => ideal Q t
local notation "K" => Ideal.map (algebraMap Q (ChartRing t)) J
local notation "U" => retainedScaledCorrectionUnit t α V

/-- The actual whole-node correction reduces to one in the coefficient quotient. -/
theorem arithmeticRetainedFullCorrection_quotient :
    Units.map (Ideal.Quotient.mk K).toMonoidHom V = 1 := by
  unfold arithmeticRetainedFullCorrection
  exact retainedFactorCorrectionUnit_reduction (S := ChartRing t ⧸ K) _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (Ideal.Quotient.mk K) (by rw [Ideal.mk_ker])

/-- The original complete retained evaluation has an explicit algebra equivalence. -/
def arithmeticRetainedFixedSmoothingEquiv : ChartRing τ ≃ₐ[Q] ChartRing t :=
  retainedFixedSmoothingEquiv t τ q α hq J (arithmeticParameterIdeal_nilpotent π m) V
    (arithmeticRetainedFullCorrection_quotient data H m k hk a)

/-- The inverse construction keeps the full original root evaluation as its forward map. -/
theorem arithmeticRetainedFixedSmoothingEquiv_toAlgHom :
    (arithmeticRetainedFixedSmoothingEquiv data H m k hk a).toAlgHom =
      retainedFixedSmoothingEvaluation t τ (q : Q) hq U := rfl

/-- Every full retained fixed-target chart, including its node, is an isomorphism. -/
instance arithmeticRetainedFixedSmoothingChart_isIso :
    IsIso (retainedFixedSmoothingChart t τ (q : Q) hq U) := by
  let e := arithmeticRetainedFixedSmoothingEquiv data H m k hk a
  change IsIso (Scheme.Spec.mapIso e.toRingEquiv.toCommRingCatIso.op).hom
  infer_instance

/-- The whole retained chart can therefore be used in a transport of gluing data. -/
def arithmeticRetainedFixedSmoothingIso :
    PolygonSmoothing.chart Q t ≅ PolygonSmoothing.chart Q τ :=
  asIso (retainedFixedSmoothingChart t τ (q : Q) hq U)

end FLT.Mazur.WeierstrassDividedDepth
