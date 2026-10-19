/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassResolvedKernelSmoothCoverage
public import FLT.Mazur.WeierstrassDividedKernelFinite

/-!
# The full retained kernel as a closed subscheme of the resolved smooth model

The source is the entire schematic closure already constructed, with its
original generic fiber and finite flat degree. The proved coverage produces
an actual closed embedding in the new relative smooth locus; no smooth-part
replacement of the integral kernel occurs.
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

/-- The entire retained kernel embeds in the actual resolved smooth open. -/
def resolvedKernelSmoothInclusion :
    finiteGlobalKernelClosure hπ data (depth / 2) (le_refl _) hΔ i ⟶
      (f).smoothLocus.toScheme :=
  IsOpenImmersion.lift (f).smoothLocus.ι c (by
    rw [Scheme.Opens.range_ι]
    exact resolvedKernelClosure_range_smooth A D hΔ i r hr hcover)

/-- The ambient inclusion is the exact full original divided kernel inclusion. -/
@[reassoc] theorem resolvedKernelSmoothInclusion_inclusion :
    resolvedKernelSmoothInclusion A D hΔ i r hr hcover ≫ (f).smoothLocus.ι = c :=
  IsOpenImmersion.lift_fac _ _ _

instance resolvedKernelSmoothInclusion_closed :
    IsClosedImmersion (resolvedKernelSmoothInclusion A D hΔ i r hr hcover) := by
  let _ : IsClosedImmersion
      (resolvedKernelSmoothInclusion A D hΔ i r hr hcover ≫ (f).smoothLocus.ι) := by
    rw [resolvedKernelSmoothInclusion_inclusion]
    infer_instance
  exact IsClosedImmersion.of_comp _ (f).smoothLocus.ι

/-- Pulling the closure back to the actual smooth open retains its entire scheme structure. -/
theorem resolvedKernelSmoothInclusion_isPullback :
    IsPullback (𝟙 _) (resolvedKernelSmoothInclusion A D hΔ i r hr hcover)
      c (f).smoothLocus.ι := by
  apply IsPullback.of_horiz_isIso_mono
  constructor
  rw [Category.id_comp, resolvedKernelSmoothInclusion_inclusion]

/-- The smooth embedding retains the same integral structure map on the full kernel. -/
@[reassoc] theorem resolvedKernelSmoothInclusion_structure :
    resolvedKernelSmoothInclusion A D hΔ i r hr hcover ≫ (f).smoothLocus.ι ≫ f =
      finiteGlobalKernelClosureStructure hπ data (depth / 2) (le_refl _) hΔ i := by
  rw [resolvedKernelSmoothInclusion_inclusion_assoc]
  rfl

/-- The original generic kernel still has exactly its original ambient inclusion. -/
@[reassoc] theorem resolvedKernelSmoothInclusion_generic :
    finiteGlobalKernelToClosure hπ data (depth / 2) (le_refl _) hΔ i ≫
      resolvedKernelSmoothInclusion A D hΔ i r hr hcover ≫ (f).smoothLocus.ι =
        i ≫ finiteGlobalGenericCurve hπ data (depth / 2) (le_refl _) hΔ := by
  rw [resolvedKernelSmoothInclusion_inclusion, finiteGlobalKernelToClosure_inclusion]

/-- The full kernel inside the resolved smooth model retains its original finite flat degree. -/
theorem resolvedKernelSmoothInclusion_degree (d : ℕ)
    (hd : FCurve.FiniteLocallyFreeDegree
      (i ≫ integralCurveStructure (W.map (algebraMap A K))) d) :
    FCurve.FiniteLocallyFreeDegree
      (resolvedKernelSmoothInclusion A D hΔ i r hr hcover ≫ (f).smoothLocus.ι ≫ f) d := by
  rw [resolvedKernelSmoothInclusion_structure]
  exact finiteGlobalKernelClosureStructure_degree hπ data (depth / 2) (le_refl _) hΔ i d hd

end FLT.Mazur.WeierstrassDividedDepth
