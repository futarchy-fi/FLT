/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassResolvedKernelSmoothEmbedding
public import FLT.Mazur.WeierstrassDividedResolvedNegation
public import FLT.Mazur.WeierstrassDividedKernelClosureNegation

/-!
# The whole resolved kernel inclusion preserves the inverse

The entire original kernel closure embeds in the resolved smooth locus,
including all special points. Its constructed inverse is the restriction
of the constructed inverse on every resolved smooth component.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {K : Type} [Field K] (A : ValuationSubring K) [IsNoetherianRing A]
  {W : WeierstrassCurve A} {π : A} {depth : ℕ} (D : SplitNodeDepth W π depth)
  (hΔ : IsUnit (W.map (algebraMap A K)).Δ)
  {H : Scheme} (i : H ⟶ integralCurve (W.map (algebraMap A K))) [IsClosedImmersion i]
  {I : Type} [Finite I] (r : I → (Spec (.of K) ⟶ H))
  (hr : ∀ a, r a ≫ i ≫ integralCurveStructure (W.map (algebraMap A K)) = 𝟙 _)
  (hcover : ∀ x : H, ∃ a z, r a z = x)
local notation "data" => splitResolutionData A D
local notation "hπ" => SplitNodeDepth.uniformizer_ne_zero D
local notation "f" => finiteGlobalStructure hπ data (depth / 2) (le_refl _)
local notation "c" => finiteGlobalKernelClosureInclusion hπ data (depth / 2) (le_refl _) hΔ i

variable (neg : H ⟶ H)
  (hn : neg ≫ i = i ≫ integralCurveNegation (W.map (algebraMap A K)))

/-- The full kernel's resolved smooth embedding commutes with the actual inverse. -/
@[reassoc] theorem resolvedKernelSmoothInclusion_negation :
    finiteKernelClosureNegation hπ data (depth / 2) (le_refl _) hΔ i neg hn ≫
        resolvedKernelSmoothInclusion A D hΔ i r hr hcover =
      resolvedKernelSmoothInclusion A D hΔ i r hr hcover ≫
        finiteResolvedNegation hπ data (depth / 2) (le_refl _) := by
  apply (cancel_mono (f).smoothLocus.ι).mp
  rw [Category.assoc, resolvedKernelSmoothInclusion_inclusion,
    finiteKernelClosureNegation_inclusion, Category.assoc, finiteResolvedNegation_inclusion,
    resolvedKernelSmoothInclusion_inclusion_assoc]

end FLT.Mazur.WeierstrassDividedDepth
