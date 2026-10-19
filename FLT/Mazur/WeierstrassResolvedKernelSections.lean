/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.DenseClosedRestriction
public import FLT.Mazur.SurjectiveDominantEpi
public import FLT.Mazur.WeierstrassResolvedKernelSmoothCoverage

/-!
# Original generic kernel points extend inside the full resolved closure

The equations of the closed kernel vanish on the dense generic source, so
each constructed ambient section factors through the full kernel itself.
The integral sections retain their original generic maps and cover every
point of the closure when the original finite generic family covers.
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
local notation "c" => finiteGlobalKernelClosureInclusion hπ data (depth / 2) (le_refl _) hΔ i
local notation "g" => finiteGlobalKernelToClosure hπ data (depth / 2) (le_refl _) hΔ i
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap A K))

/-- The original fraction-field base is schematically dense in the valuation spectrum. -/
local instance resolvedKernelGenericBase_dense : IsSchemeTheoreticallyDominant q :=
  SurjectiveDominantEpi.spec_schematic (algebraMap A K) (IsFractionRing.injective A K)

/-- Restrict the actual original point section to the retained full kernel by its equations. -/
def resolvedKernelSection (a : I) : Spec (.of A) ⟶
    finiteGlobalKernelClosure hπ data (depth / 2) (le_refl _) hΔ i :=
  DenseClosedRestriction.lift q c (resolvedKernelPointSection A D hΔ i r hr a)
    (r a ≫ g) (by
      rw [resolvedKernelPointSection_generic, Category.assoc,
        finiteGlobalKernelToClosure_inclusion]
      rfl)

/-- The integral kernel section recovers the actual point section on the whole divided model. -/
@[reassoc] theorem resolvedKernelSection_inclusion (a : I) :
    resolvedKernelSection A D hΔ i r hr a ≫ c = resolvedKernelPointSection A D hΔ i r hr a :=
  DenseClosedRestriction.lift_inclusion _ _ _ _ _

/-- Generic restriction retains the same original kernel point, including its map to the closure. -/
@[reassoc] theorem resolvedKernelSection_generic (a : I) :
    q ≫ resolvedKernelSection A D hΔ i r hr a = r a ≫ g :=
  DenseClosedRestriction.dense_lift _ _ _ _ _

/-- Each integral kernel point is a section over the original valuation base. -/
@[reassoc] theorem resolvedKernelSection_structure (a : I) :
    resolvedKernelSection A D hΔ i r hr a ≫
      finiteGlobalKernelClosureStructure hπ data (depth / 2) (le_refl _) hΔ i = 𝟙 _ := by
  rw [finiteGlobalKernelClosureStructure, resolvedKernelSection_inclusion_assoc,
    resolvedKernelPointSection_structure]

variable [IsClosedImmersion i] [Finite I]

/-- The actual integral kernel sections cover every point of the full retained kernel. -/
theorem resolvedKernelSection_cover (hcover : ∀ x : H, ∃ a z, r a z = x)
    (x : finiteGlobalKernelClosure hπ data (depth / 2) (le_refl _) hΔ i) :
    ∃ a z, resolvedKernelSection A D hΔ i r hr a z = x := by
  have hx := resolvedKernelClosure_range_sections A D hΔ i r hr hcover ⟨x, rfl⟩
  obtain ⟨a, z, hz⟩ := Set.mem_iUnion.mp hx
  refine ⟨a, z, (c).isClosedEmbedding.injective ?_⟩
  have he := congrArg (fun m : Spec (.of A) ⟶
    finiteGlobalModel hπ data (depth / 2) (le_refl _) => m z)
      (resolvedKernelSection_inclusion A D hΔ i r hr a)
  exact he.trans hz

end FLT.Mazur.WeierstrassDividedDepth
