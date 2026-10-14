/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticResolvedIdentityChart

/-!
# Exactly the original smooth reductions lie in the resolved identity chart

Factoring the full proper specialization through the actual identity torus
is equivalent to the arithmetic E₀ condition. The factor retains the residue
structure map and reconstructs the original point of the resolved smooth locus.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] (A : ValuationSubring K)
  {W : WeierstrassCurve A} {π : A} {depth : ℕ} (D : SplitNodeDepth W π depth)
local notation "F" => ResidueField A
local notation "data" => splitResolutionData A D
local notation "hπ" => SplitNodeDepth.uniformizer_ne_zero D
local notation "p" => resolvedSplitStructure A D
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap A F))
local notation "f" => finiteGlobalStructure hπ data (depth / 2) (le_refl _)
local notation "c" => finiteGlobalContraction hπ data (depth / 2) (le_refl _)
local notation "sp" => finitePointSpecialization A hπ data (depth / 2) (le_refl _)

/-- The entire specialized morphism lies in the identity chart exactly for arithmetic E₀. -/
theorem resolvedIdentityChart_contains_iff
    (P : (W.map (algebraMap A K)).toProjective.Point) :
    Set.range (sp P) ⊆ Set.range (resolvedIdentityChart A D) ↔ SmoothReduction A W P := by
  have hc := finitePointSpecialization_contraction A hπ data (depth / 2) (le_refl _) P
  rw [resolvedIdentityChart_range, ← integralPointSpecialization_smooth_iff]
  rw [Set.range_subset_iff, Set.range_subset_iff]
  change (∀ x, ((sp P) ≫ pullback.snd q f ≫ c) x ∈ integralSmoothOpen W) ↔ _
  exact Iff.of_eq (congrArg
    (fun g : Spec (.of F) ⟶ integralCurve W => ∀ x, g x ∈ integralSmoothOpen W) hc)

/-- The full torus coordinate morphism of an original E₀ point. -/
def resolvedIdentityPointCoordinate (P : ellipticE0 A W) :
    Spec (.of F) ⟶ Spec (.of F[T;T⁻¹]) :=
  IsOpenImmersion.lift (resolvedIdentityChart A D) (sp P.val)
    ((resolvedIdentityChart_contains_iff A D P.val).mpr P.property)

/-- The actual identity-chart coordinate reconstructs unrestricted proper specialization. -/
@[reassoc] theorem resolvedIdentityPointCoordinate_chart (P : ellipticE0 A W) :
    resolvedIdentityPointCoordinate A D P ≫ resolvedIdentityChart A D = sp P.val :=
  IsOpenImmersion.lift_fac _ _ _

/-- The original identity coordinate is a residue-field point of the torus. -/
@[reassoc] theorem resolvedIdentityPointCoordinate_structure (P : ellipticE0 A W) :
    resolvedIdentityPointCoordinate A D P ≫ (MultiplicativeGroupScheme.gm F).hom = 𝟙 _ := by
  rw [← resolvedIdentityChart_structure A D, ← Category.assoc,
    resolvedIdentityPointCoordinate_chart]
  exact finitePointSpecialization_structure A hπ data (depth / 2) (le_refl _) P.val

/-- The identity torus also reconstructs the original resolved smooth point. -/
@[reassoc] theorem resolvedIdentityPointCoordinate_smoothChart (P : ellipticE0 A W) :
    resolvedIdentityPointCoordinate A D P ≫ resolvedIdentitySmoothChart A D =
      resolvedSplitSmoothPoint A D P.val := by
  apply (cancel_mono (p).smoothLocus.ι).mp
  rw [Category.assoc, resolvedIdentitySmoothChart_inclusion,
    resolvedSplitSmoothPoint_inclusion, resolvedIdentityPointCoordinate_chart]

/-- A factor through the identity torus detects, rather than assumes, original smooth reduction. -/
theorem resolvedIdentityChart_factors_iff
    (P : (W.map (algebraMap A K)).toProjective.Point) :
    (∃ t : Spec (.of F) ⟶ Spec (.of F[T;T⁻¹]),
      t ≫ resolvedIdentityChart A D = sp P) ↔ SmoothReduction A W P := by
  constructor
  · rintro ⟨t, ht⟩
    apply (resolvedIdentityChart_contains_iff A D P).mp
    rintro _ ⟨x, rfl⟩
    rw [← ht]
    exact ⟨t x, rfl⟩
  · intro hP
    exact ⟨resolvedIdentityPointCoordinate A D ⟨P, hP⟩,
      resolvedIdentityPointCoordinate_chart A D ⟨P, hP⟩⟩

/-- Identity coordinates identify exactly the points with the same original smooth reduction. -/
theorem resolvedIdentityPointCoordinate_eq_iff (P Q : ellipticE0 A W) :
    resolvedIdentityPointCoordinate A D P = resolvedIdentityPointCoordinate A D Q ↔
      smoothReductionHom A W P = smoothReductionHom A W Q := by
  rw [← cancel_mono (resolvedIdentityChart A D), resolvedIdentityPointCoordinate_chart,
    resolvedIdentityPointCoordinate_chart, finitePointSpecialization_e0,
    finitePointSpecialization_e0, e0FiniteClosedPoint_eq_iff]

end FLT.Mazur.WeierstrassDividedDepth
