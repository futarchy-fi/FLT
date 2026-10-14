/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearResidueStrictPositiveInitialBoundary
public import FLT.Mazur.WeierstrassCoefficientShearInitialAtlasPullback
public import FLT.Mazur.WeierstrassCoefficientShearInitialLaterAtlasPullback
public import FLT.Mazur.WeierstrassCoefficientShearResidueAtlasAdjacentPullback
import all FLT.Mazur.WeierstrassCoefficientShearResidueStrictPositiveInitialBoundary
public import FLT.Mazur.WeierstrassCoefficientShearResidueStrictPositiveAtlasLines
public import FLT.Mazur.WeierstrassCoefficientShearInitialBoundaryDescent
public import FLT.Mazur.WeierstrassCoefficientShearInitialTensorConicComparison
import all FLT.Mazur.WeierstrassCoefficientShearResidueInitialCoconeDescent
import all FLT.Mazur.WeierstrassCoefficientShearResidueStrictPositiveAtlasMaps
import all FLT.Mazur.WeierstrassCoefficientShearResidueTerminalDescent
import all FLT.Mazur.WeierstrassCoefficientShearResidueInteriorDescent
import all FLT.Mazur.WeierstrassCoefficientShearRetainedEquationDescent

/-!
# Every actual full initial and retained atlas pullback is compatible

The first retained chart uses the full original boundary theorem. All later
retained charts have empty full intersections with the initial chart.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0)
  (hm : maximalIdeal R = Ideal.span {π}) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (s : ℕ) (hs : s + 1 ≤ n) (hk : 2 * (start + (s + 1)) < depth)
  (hstart : 0 < start)
  (h3 : W.a₃ ∈ maximalIdeal R ^ (depth + 1))
  (h4 : W.a₄ ∈ maximalIdeal R ^ (depth + 1))
  (h6 : W.a₆ ∈ maximalIdeal R ^ depth)
  (hc : IsUnit W.c₄)
local notation "V" => W.map (residue R)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial V)
local notation "r" => AdjoinRoot.root (nodeTangentPolynomial V)
variable [Fact (Irreducible (nodeTangentPolynomial (W.map (residue R))))]
open WeierstrassModificationX WeierstrassSuccessiveX WeierstrassDilatation
local notation "a" => residueTangentComponentUnit W h3 h4 hc
local notation "ha" => residueTangentComponentUnit_val W h3 h4 hc
variable (C : PushoutCocone (PolygonPinching.toComponents
    (AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))) (2 * s + 5) (by omega))
  (PolygonPinching.toNodes
    (AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))) (2 * s + 5)))
local notation "hp" => residueTangentEquation_zero W π
  (hm ▸ Ideal.mem_span_singleton_self π)
local notation "D" => coefficientShearResidueStrictPositiveAtlasCoconeMap
  hπ hm data s hs hk hstart h3 h4 h6 hc C
local notation "atlas" => coefficientShearAtlasMap hπ data Q r (s + 1) hs

/-- The complete first retained intersection satisfies the actual cocone equation. -/
theorem coefficientShearResidueStrictPositiveAtlasCoconeMap_initial_first_pullback :
    pullback.fst (atlas (.inl 2)) (atlas (.inr 0)) ≫ D (.inl 2) =
      pullback.snd (atlas (.inl 2)) (atlas (.inr 0)) ≫ D (.inr 0) := by
  apply fullAtlasPullback_compatible
    (coefficientShearInitialAtlas_isPullback hπ data Q r (s + 1) hs (by omega))
  simpa only [Category.assoc] using
    coefficientShearResidueStrictPositiveAtlasCoconeMap_initial_boundary
      hπ hm data s hs hk hstart h3 h4 h6 hc C

/-- Every full initial/retained intersection satisfies the actual cocone equation. -/
theorem coefficientShearResidueStrictPositiveAtlasCoconeMap_initial_retained_pullback
    (i : Fin (s + 1)) :
    pullback.fst (atlas (.inl 2)) (atlas (.inr i)) ≫ D (.inl 2) =
      pullback.snd (atlas (.inl 2)) (atlas (.inr i)) ≫ D (.inr i) := by
  by_cases hi : i = 0
  · subst i
    exact coefficientShearResidueStrictPositiveAtlasCoconeMap_initial_first_pullback
      hπ hm data s hs hk hstart h3 h4 h6 hc C
  · exact coefficientShearAtlas_initial_later_compatible
      hπ data Q r (s + 1) hs i (by simpa using Fin.pos_iff_ne_zero.mpr hi) hp _ _

/-- Reversing any initial/retained pair preserves the full cocone equation. -/
theorem coefficientShearResidueStrictPositiveAtlasCoconeMap_retained_initial_pullback
    (i : Fin (s + 1)) :
    pullback.fst (atlas (.inr i)) (atlas (.inl 2)) ≫ D (.inr i) =
      pullback.snd (atlas (.inr i)) (atlas (.inl 2)) ≫ D (.inl 2) := by
  apply (cancel_epi (pullbackSymmetry (atlas (.inl 2)) (atlas (.inr i))).hom).mp
  simpa only [pullbackSymmetry_hom_comp_fst_assoc, pullbackSymmetry_hom_comp_snd_assoc]
    using (coefficientShearResidueStrictPositiveAtlasCoconeMap_initial_retained_pullback
      hπ hm data s hs hk hstart h3 h4 h6 hc C i).symm

end FLT.Mazur.WeierstrassDividedDepth
