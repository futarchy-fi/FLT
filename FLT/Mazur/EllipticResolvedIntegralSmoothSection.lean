/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticResolvedSmoothPoint
public import FLT.Mazur.SchemeSmoothLocusCartesian
public import FLT.Mazur.WeierstrassDividedGlobalFiniteFlat

/-!
# Whole integral sections in the resolved model's own smooth locus

The chart calculation at the closed fiber implies relative smoothness along
an entire original point section. This includes sections reducing to the old
singular point: their final divided charts, rather than the old smooth open,
provide the required smoothness.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] (A : ValuationSubring K) [IsNoetherianRing A]
  {W : WeierstrassCurve A} {π : A} {depth : ℕ} (D : SplitNodeDepth W π depth)
local notation "data" => splitResolutionData A D
local notation "hπ" => SplitNodeDepth.uniformizer_ne_zero D
local notation "f" => finiteGlobalStructure hπ data (depth / 2) (le_refl _)
local notation "k" => ResidueField A
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap A k))

/-- Every original point section lies in the actual relative smooth locus of the full model. -/
theorem resolvedIntegralPoint_range_smooth
    (P : (W.map (algebraMap A K)).toProjective.Point) :
    Set.range (finitePointSection A hπ data (depth / 2) (le_refl _) P) ⊆ (f).smoothLocus := by
  let t := finitePointSection A hπ data (depth / 2) (le_refl _) P
  have hc : t (closedPoint A) ∈ (f).smoothLocus := by
    have hx := finitePointSpecialization_resolved_smooth A hπ D data P (closedPoint k)
    dsimp only at hx
    have he := smoothLocus_preimage_of_isPullback (IsPullback.of_hasPullback q f).flip
    rw [← he] at hx
    change (finitePointSpecialization A hπ data (depth / 2) (le_refl _) P ≫
      pullback.snd q f) (closedPoint k) ∈ (f).smoothLocus at hx
    have hp := congrArg (fun m : Spec (.of k) ⟶
        finiteGlobalModel hπ data (depth / 2) (le_refl _) => m (closedPoint k))
      (finitePointSpecialization_projection A hπ data (depth / 2) (le_refl _) P)
    change _ = t (PrimeSpectrum.comap (residue A) (closedPoint k)) at hp
    rw [IsLocalRing.PrimeSpectrum.comap_residue] at hp
    exact hp ▸ hx
  rintro _ ⟨x, rfl⟩
  exact ((specializes_closedPoint x).map t.continuous).mem_open (f).smoothLocus.isOpen hc

/-- The original proper section factors through the full model's own relative smooth open. -/
def resolvedIntegralSmoothSection
    (P : (W.map (algebraMap A K)).toProjective.Point) :
    Spec (.of A) ⟶ (f).smoothLocus.toScheme :=
  IsOpenImmersion.lift (f).smoothLocus.ι
    (finitePointSection A hπ data (depth / 2) (le_refl _) P) (by
      rw [Scheme.Opens.range_ι]
      exact resolvedIntegralPoint_range_smooth A D P)

/-- The factorization retains the original unrestricted proper section. -/
@[reassoc] theorem resolvedIntegralSmoothSection_inclusion
    (P : (W.map (algebraMap A K)).toProjective.Point) :
    resolvedIntegralSmoothSection A D P ≫ (f).smoothLocus.ι =
      finitePointSection A hπ data (depth / 2) (le_refl _) P :=
  IsOpenImmersion.lift_fac _ _ _

/-- The smooth lift remains a section over the exact original valuation base. -/
@[reassoc] theorem resolvedIntegralSmoothSection_structure
    (P : (W.map (algebraMap A K)).toProjective.Point) :
    resolvedIntegralSmoothSection A D P ≫ (f).smoothLocus.ι ≫ f = 𝟙 _ := by
  rw [resolvedIntegralSmoothSection_inclusion_assoc, finitePointSection_structure]

end FLT.Mazur.WeierstrassDividedDepth
