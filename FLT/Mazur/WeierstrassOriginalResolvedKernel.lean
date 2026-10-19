/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassResolvedKernelSmoothEmbedding
public import FLT.Mazur.WeierstrassLocalKernelCoefficientSquare
public import FLT.Mazur.FiniteLocallyFreeDegreeAffine

/-!
# Resolving the full original kernel without losing its degree

Apply the split-depth resolution to the local realization of the original
embedded kernel. Its closed embedding in the resolved smooth open retains
both its exact generic inclusion and the original finite locally free degree.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry WeierstrassCurve
namespace FLT.Mazur.WeierstrassOriginalResolvedKernel
open WeierstrassIntegralChart WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
variable {R K : Type} [CommRing R] [Field K] [Algebra R K]
  (A : ValuationSubring K) [IsNoetherianRing A]
  (E : WeierstrassCurve R) [E.IsElliptic] (W : WeierstrassCurve A) (C : VariableChange K)
  (hC : C • E.map (algebraMap R K) = W.map (algebraMap A K))
  {π : A} {depth : ℕ} (D : SplitNodeDepth W π depth)
  {H : Scheme} (i : H ⟶ integralCurve E) [IsClosedImmersion i]
  {I : Type} [Finite I] (r : I → (Spec (.of K) ⟶ localGenericKernel E W C hC i))
  (hr : ∀ a, r a ≫ localGenericKernelInclusion E W C hC i ≫
    integralCurveStructure (W.map (algebraMap A K)) = 𝟙 _)
  (hc : ∀ x : localGenericKernel E W C hC i, ∃ a z, r a z = x)

omit [IsNoetherianRing A] in
include hC in
/-- The original elliptic equation supplies the generic discriminant unit for resolution. -/
theorem genericDiscriminant : IsUnit (W.map (algebraMap A K)).Δ := by
  let _ : (W.map (algebraMap A K)).IsElliptic := by rw [← hC]; infer_instance
  exact (W.map (algebraMap A K)).isUnit_Δ

local notation "hΔ" => genericDiscriminant A E W C hC
local notation "data" => splitResolutionData A D
local notation "hπ" => SplitNodeDepth.uniformizer_ne_zero D
local notation "f" => finiteGlobalStructure hπ data (depth / 2) (le_refl _)
local notation "j" => localGenericKernelInclusion E W C hC i

/-- Embed the entire original local kernel closure in the resolved relative smooth open. -/
def inclusion : finiteGlobalKernelClosure hπ data (depth / 2) (le_refl _) hΔ j ⟶
    (f).smoothLocus.toScheme :=
  resolvedKernelSmoothInclusion A D hΔ j r hr hc

instance inclusion_closed : IsClosedImmersion (inclusion A E W C hC D i r hr hc) :=
  resolvedKernelSmoothInclusion_closed A D hΔ j r hr hc

/-- The closure's generic inclusion is exactly the local realization of the original kernel. -/
@[reassoc] theorem inclusion_generic :
    finiteGlobalKernelToClosure hπ data (depth / 2) (le_refl _) hΔ j ≫
      inclusion A E W C hC D i r hr hc ≫ (f).smoothLocus.ι =
        j ≫ finiteGlobalGenericCurve hπ data (depth / 2) (le_refl _) hΔ :=
  resolvedKernelSmoothInclusion_generic A D hΔ j r hr hc

/-- The original degree is retained by coefficient extension and by the full smooth embedding. -/
theorem inclusion_degree (d : ℕ)
    (hd : FCurve.FiniteLocallyFreeDegree (i ≫ integralCurveStructure E) d) :
    FCurve.FiniteLocallyFreeDegree
      (inclusion A E W C hC D i r hr hc ≫ (f).smoothLocus.ι ≫ f) d := by
  apply resolvedKernelSmoothInclusion_degree
  exact FCurve.finiteLocallyFreeDegree_of_isPullback
    (WeierstrassLocalKernelCoefficientSquare.isPullback E W C hC i) d hd

end FLT.Mazur.WeierstrassOriginalResolvedKernel
