/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedKernelSmoothRecovery
public import FLT.Mazur.WeierstrassValuationClosureSmoothFlat
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Dense smooth pairs in the full resolved kernel action domain

The original smooth kernel is schematically dense in the entire divided
closure. Its self-product is dense in the mixed product with that full closure,
which allows its existing multiplication to detect closed equations there.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R K : Type} [CommRing R] [IsDomain R] [ValuationRing R] [IsNoetherianRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j ≤ n)
  (hΔ : IsUnit (W.map (algebraMap R K)).Δ)
  {H : Scheme} (i : H ⟶ integralCurve (W.map (algebraMap R K))) [IsClosedImmersion i]
local notation "s" => genericClosureSmoothStructure W i
local notation "f" => finiteGlobalKernelClosureStructure hπ data j hj hΔ i
local notation "e" => finiteGlobalKernelSmoothEmbedding hπ data j hj hΔ i

/-- The full original smooth intersection is dense in the entire divided kernel closure. -/
instance finiteGlobalKernelSmoothEmbedding_dense : IsSchemeTheoreticallyDominant e := by
  constructor
  have he := congrArg Scheme.Hom.ker
    (genericKernelToClosureSmooth_dividedEmbedding hπ data j hj hΔ i)
  simpa only [Scheme.Hom.ker_comp, Scheme.Hom.ker_eq_bot,
    Scheme.IdealSheafData.map_bot] using he

/-- The original smooth intersection is a quasi-compact open in the full divided closure. -/
instance finiteGlobalKernelSmoothEmbedding_quasiCompact : QuasiCompact e := by
  let _ : IsLocallyNoetherian (finiteGlobalKernelClosure hπ data j hj hΔ i) :=
    LocallyOfFiniteType.isLocallyNoetherian f
  infer_instance

/-- Include smooth kernel pairs into the actual mixed smooth-kernel/full-kernel product. -/
def finiteGlobalMixedKernelPair : pullback s s ⟶ pullback s f :=
  pullback.lift (pullback.fst s s) (pullback.snd s s ≫ e) (by
    rw [Category.assoc, finiteGlobalKernelSmoothEmbedding_structure]
    exact pullback.condition)

omit [IsNoetherianRing R] [IsFractionRing R K] in
/-- The first input remains the original smooth kernel. -/
@[reassoc] theorem finiteGlobalMixedKernelPair_fst :
    finiteGlobalMixedKernelPair hπ data j hj hΔ i ≫ pullback.fst s f = pullback.fst s s :=
  pullback.lift_fst _ _ _

omit [IsNoetherianRing R] [IsFractionRing R K] in
/-- The second input is included in the full divided closure without changing its map. -/
@[reassoc] theorem finiteGlobalMixedKernelPair_snd :
    finiteGlobalMixedKernelPair hπ data j hj hΔ i ≫ pullback.snd s f =
      pullback.snd s s ≫ e := pullback.lift_snd _ _ _

omit [IsNoetherianRing R] [IsFractionRing R K] in
/-- The mixed pair inclusion is the actual base change of the original smooth kernel embedding. -/
theorem finiteGlobalMixedKernelPair_isPullback :
    IsPullback (pullback.snd s s) (finiteGlobalMixedKernelPair hπ data j hj hΔ i)
      e (pullback.snd s f) := by
  apply (IsPullback.paste_vert_iff (IsPullback.of_hasPullback s f).flip
    (finiteGlobalMixedKernelPair_snd hπ data j hj hΔ i).symm).mp
  simpa only [finiteGlobalMixedKernelPair_fst, finiteGlobalKernelSmoothEmbedding_structure] using
    (IsPullback.of_hasPullback s s).flip

/-- Flatness of the original smooth kernel makes the smooth pairs schematically dense. -/
theorem finiteGlobalMixedKernelPair_dense
    [Flat (i ≫ integralCurveStructure (W.map (algebraMap R K)))] :
    IsSchemeTheoreticallyDominant (finiteGlobalMixedKernelPair hπ data j hj hΔ i) := by
  let _ := genericClosureSmoothStructure_flat_valuation W i
  exact IsSchemeTheoreticallyDominant.of_isPullback
    (finiteGlobalMixedKernelPair_isPullback hπ data j hj hΔ i)

end FLT.Mazur.WeierstrassDividedDepth
