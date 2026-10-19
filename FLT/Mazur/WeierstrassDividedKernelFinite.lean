/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedKernelClosure
public import FLT.Mazur.WeierstrassValuationKernelClosureDegree

/-!
# Finite flat degree of the full divided kernel closure

The entire closure in the actual divided model is flat by schematic density
and finite by its properness and original finite generic fiber. Over a
Noetherian valuation base it retains the original finite locally free degree.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false

variable {R K : Type} [CommRing R] [IsDomain R] [IsBezout R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j ≤ n)
  (hΔ : IsUnit (W.map (algebraMap R K)).Δ)
  {H : Scheme} (i : H ⟶ integralCurve (W.map (algebraMap R K))) [IsClosedImmersion i]

/-- Flatness of the entire divided closure, without any smooth-locus restriction. -/
theorem finiteGlobalKernelClosureStructure_flat
    [Flat (i ≫ integralCurveStructure (W.map (algebraMap R K)))] :
    Flat (finiteGlobalKernelClosureStructure hπ data j hj hΔ i) := by
  let e := (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv
  let _ : IsDomain Γ(Spec (.of R), ⊤) := e.toMulEquiv.isDomain _
  let _ : IsBezout Γ(Spec (.of R), ⊤) := e.symm.surjective.isBezout e.symm.toRingHom
  let _ : Flat (Spec.map (CommRingCat.ofHom (algebraMap R K))) :=
    Flat.SpecMap_iff.mpr
      (RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat K (nonZeroDivisors R)))
  let _ : Flat (finiteGlobalKernelToClosure hπ data j hj hΔ i ≫
      finiteGlobalKernelClosureStructure hπ data j hj hΔ i) := by
    rw [finiteGlobalKernelToClosure_structure]
    infer_instance
  exact SchematicDenseBezoutFlat.flat (finiteGlobalKernelToClosure hπ data j hj hΔ i)
    (finiteGlobalKernelClosureStructure hπ data j hj hΔ i)

variable [ValuationRing R]

/-- The full divided closure is finite over the original valuation base. -/
theorem finiteGlobalKernelClosureStructure_finite
    [Flat (i ≫ integralCurveStructure (W.map (algebraMap R K)))]
    [IsFinite (i ≫ integralCurveStructure (W.map (algebraMap R K)))] :
    IsFinite (finiteGlobalKernelClosureStructure hπ data j hj hΔ i) := by
  let _ := finiteGlobalKernelClosureStructure_flat hπ data j hj hΔ i
  let _ : IsFinite (pullback.snd (finiteGlobalKernelClosureStructure hπ data j hj hΔ i)
      (Spec.map (CommRingCat.ofHom (algebraMap R K)))) := by
    rw [← (finiteGlobalKernelClosureStructure_isPullback hπ data j hj hΔ i).isoPullback_inv_snd]
    infer_instance
  exact ProperFlatValuationFinite.finite_of_generic (K := K)
    (finiteGlobalKernelClosureStructure hπ data j hj hΔ i)

/-- The entire divided closure has exactly the original generic degree. -/
theorem finiteGlobalKernelClosureStructure_degree [IsNoetherianRing R] (d : ℕ)
    (hd : FCurve.FiniteLocallyFreeDegree
      (i ≫ integralCurveStructure (W.map (algebraMap R K))) d) :
    FCurve.FiniteLocallyFreeDegree (finiteGlobalKernelClosureStructure hπ data j hj hΔ i) d := by
  let _ : IsFinite (i ≫ integralCurveStructure (W.map (algebraMap R K))) := hd.1
  let _ : Flat (i ≫ integralCurveStructure (W.map (algebraMap R K))) := hd.2.1
  let _ := finiteGlobalKernelClosureStructure_finite hπ data j hj hΔ i
  let _ := finiteGlobalKernelClosureStructure_flat hπ data j hj hΔ i
  refine ⟨inferInstance, inferInstance, inferInstance, ?_⟩
  intro x
  let y := IsLocalRing.closedPoint K
  have he := Scheme.Hom.finrank_of_isPullback _ _ _ _
    (finiteGlobalKernelClosureStructure_isPullback hπ data j hj hΔ i) y
  calc
    (finiteGlobalKernelClosureStructure hπ data j hj hΔ i).finrank x =
        (finiteGlobalKernelClosureStructure hπ data j hj hΔ i).finrank
          (Spec.map (CommRingCat.ofHom (algebraMap R K)) y) :=
      (finiteGlobalKernelClosureStructure hπ data j hj hΔ i).isLocallyConstant_finrank
        |>.apply_eq_of_preconnectedSpace _ _
    _ = d := he.symm.trans (hd.2.2.2 y)

end FLT.Mazur.WeierstrassDividedDepth
