/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticResolvedIntegralSmoothSection
public import FLT.Mazur.SchematicClosureFiniteSections
public import FLT.Mazur.WeierstrassGenericKernelRationalPoint

/-!
# Full kernel coverage in the resolved model's own smooth locus

A finite rational cover of the original generic kernel gives actual original
point sections. The divided chart calculations put every such section in the
relative smooth locus. Closedness of their finite union covers the full
schematic closure, including points above the original singular locus.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {K : Type} [Field K] (A : ValuationSubring K)
  {W : WeierstrassCurve A} {π : A} {depth : ℕ} (D : SplitNodeDepth W π depth)
  (hΔ : IsUnit (W.map (algebraMap A K)).Δ)
  {H : Scheme} (i : H ⟶ integralCurve (W.map (algebraMap A K)))
  {I : Type} (r : I → (Spec (.of K) ⟶ H))
  (hr : ∀ a, r a ≫ i ≫ integralCurveStructure (W.map (algebraMap A K)) = 𝟙 _)
local notation "data" => splitResolutionData A D
local notation "hπ" => SplitNodeDepth.uniformizer_ne_zero D
local notation "f" => finiteGlobalStructure hπ data (depth / 2) (le_refl _)
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap A K))

/-- The actual proper section attached to each original rational kernel point. -/
def resolvedKernelPointSection (a : I) :
    Spec (.of A) ⟶ finiteGlobalModel hπ data (depth / 2) (le_refl _) :=
  finitePointSection A hπ data (depth / 2) (le_refl _)
    (genericKernelProjectivePoint W hΔ i (r a) (hr a))

/-- Its base remains the original valuation spectrum. -/
@[reassoc] theorem resolvedKernelPointSection_structure (a : I) :
    resolvedKernelPointSection A D hΔ i r hr a ≫ f = 𝟙 _ :=
  finitePointSection_structure A hπ data (depth / 2) (le_refl _) _

/-- Generic restriction is the exact original kernel point in the actual divided model. -/
@[reassoc] theorem resolvedKernelPointSection_generic (a : I) :
    q ≫ resolvedKernelPointSection A D hΔ i r hr a =
      r a ≫ finiteGlobalGenericKernel hπ data (depth / 2) (le_refl _) hΔ i := by
  rw [resolvedKernelPointSection, finitePointSection_generic,
    genericKernelProjectivePoint_smooth_assoc]
  rfl

variable [IsNoetherianRing A]

/-- The final divided charts put every original kernel point section in the smooth locus. -/
theorem resolvedKernelPointSection_range_smooth (a : I) :
    Set.range (resolvedKernelPointSection A D hΔ i r hr a) ⊆ (f).smoothLocus :=
  resolvedIntegralPoint_range_smooth A D _

variable [IsClosedImmersion i] [Finite I]

include hr in
omit [IsNoetherianRing A] in
/-- Finite rational generic support covers the entire original schematic kernel closure. -/
theorem resolvedKernelClosure_range_sections
    (hcover : ∀ x : H, ∃ a z, r a z = x) :
    Set.range (finiteGlobalKernelClosureInclusion hπ data (depth / 2) (le_refl _) hΔ i) ⊆
      ⋃ a, Set.range (resolvedKernelPointSection A D hΔ i r hr a) := by
  apply SchematicClosureFiniteSections.image_range_subset f
    (finiteGlobalGenericKernel hπ data (depth / 2) (le_refl _) hΔ i)
    (resolvedKernelPointSection A D hΔ i r hr)
    (resolvedKernelPointSection_structure A D hΔ i r hr)
  rintro _ ⟨x, rfl⟩
  obtain ⟨a, z, rfl⟩ := hcover x
  apply Set.mem_iUnion.mpr
  refine ⟨a, q z, ?_⟩
  exact congrArg (fun m : Spec (.of K) ⟶
    finiteGlobalModel hπ data (depth / 2) (le_refl _) => m z)
      (resolvedKernelPointSection_generic A D hΔ i r hr a)

include hr in
/-- The full retained kernel lies in the resolved smooth locus after generic splitting. -/
theorem resolvedKernelClosure_range_smooth
    (hcover : ∀ x : H, ∃ a z, r a z = x) :
    Set.range (finiteGlobalKernelClosureInclusion hπ data (depth / 2) (le_refl _) hΔ i) ⊆
      (f).smoothLocus := by
  apply (resolvedKernelClosure_range_sections A D hΔ i r hr hcover).trans
  exact Set.iUnion_subset (resolvedKernelPointSection_range_smooth A D hΔ i r hr)

end FLT.Mazur.WeierstrassDividedDepth
