/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearResidueZeroInfinityParameter
public import FLT.Mazur.WeierstrassCoefficientShearResidueZeroInitialPullbacks
import all FLT.Mazur.WeierstrassCoefficientShearResidueZeroAtlasCoconeMaps
import all FLT.Mazur.WeierstrassCoefficientShearResidueZeroInfinityParameter
import all FLT.Mazur.WeierstrassCoefficientShearResidueZeroExteriorCoconeMaps

/-!
# Full original start-zero initial and infinity cocone compatibility

Both chart maps agree on their entire shifted scheme-theoretic intersection,
including when the first retained conic has nonzero constant.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0)
  (hm : maximalIdeal R = Ideal.span {π}) {n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (s : ℕ) (hs : s + 1 ≤ n)
  (he : 2 * (0 + (s + 1)) = depth)
  (h3 : W.a₃ ∈ maximalIdeal R ^ (depth + 1))
  (h4 : W.a₄ ∈ maximalIdeal R ^ (depth + 1))
  (h6next : W.a₆ ∉ maximalIdeal R ^ (depth + 1)) (hc : IsUnit W.c₄)
local notation "V" => W.map (residue R)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial V)
local notation "r" => AdjoinRoot.root (nodeTangentPolynomial V)
variable [Fact (Irreducible (nodeTangentPolynomial (W.map (residue R))))]
variable (C : PushoutCocone (PolygonPinching.toComponents
    (AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))) (2 * s + 2)
    (Nat.zero_lt_succ (2 * s + 1)))
  (PolygonPinching.toNodes
    (AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))) (2 * s + 2)))
local notation "F" => PolygonCyclicPushout.inputComponent Q (2 * s + 2) C.inl
local notation "w" => fun i => by
  simpa only [PolygonCyclicAtlas.next_eq_rotate] using
    PolygonCyclicPushout.input_condition Q (2 * s + 2) (by omega) C.inl C.inr C.condition i

open WeierstrassModificationX WeierstrassSuccessiveX
local notation "e" => data ⟨1, by omega⟩
local notation "lin" => nodalDepth_tangent_linear_zero hπ hm e (by dsimp; omega) h3 h4
local notation "hp" => residueTangentEquation_zero W π
  (hm ▸ Ideal.mem_span_singleton_self π)
local notation "hr" => residueTangentEquation_root W
local notation "hscale" => show algebraMap R Q (π ^ (0 + 0)) = 1 from by simp
local notation "a" => residueTangentComponentUnit W h3 h4 hc
local notation "ha" => residueTangentComponentUnit_val W h3 h4 hc
local notation "U" => rootShearCurve (W.map (algebraMap R Q)) r
local notation "P" => SlopeOpen (U).a₁
local notation "z" => (slopeZ (U).a₁ * (slopeZ (U).a₁ + algebraMap Q P (U).a₁)) *
  (slopeZ (U).a₁ + algebraMap Q P r)
local notation "p" => PrincipalOpenTransport.inclusion z
local notation "I" => coefficientShearResidueZeroInitialIso hπ hm data s hs
local notation "b" => coefficientShearResidueZeroInfinityBoundary hπ hm data s hs
local notation "D" => coefficientShearResidueZeroAtlasCoconeMap
  hπ hm data s hs he h3 h4 h6next hc C
local notation "atlas" => coefficientShearAtlasMap hπ data Q r (s + 1) hs

/-- Both original chart maps agree on the complete shifted vertical boundary. -/
theorem coefficientShearResidueZeroAtlasCoconeMap_infinity_initial_boundary :
    b ≫ D (.inl 0) = p ≫ (I).hom ≫ D (.inl 2) := by
  rw [coefficientShearResidueZeroAtlasCoconeMap_infinity,
    coefficientShearResidueZeroAtlasCoconeMap_initial,
    coefficientShearResidueZeroInitialCoconeDesc_slope,
    coefficientShearResidueZeroInfinityCoconeDesc]
  have H := congrArg (· ≫ (ProjectiveLine.slopeNormalizationIso a).hom ≫ F 0)
    (coefficientShearResidueZeroInfinityBoundary_parameter
      hπ hm data s hs (lin).1 (lin).2 a ha)
  simpa only [Category.assoc] using H

/-- The entire infinity/initial categorical pullback satisfies the cocone equation. -/
theorem coefficientShearResidueZeroAtlasCoconeMap_infinity_initial_pullback :
    pullback.fst (atlas (.inl 0)) (atlas (.inl 2)) ≫ D (.inl 0) =
      pullback.snd (atlas (.inl 0)) (atlas (.inl 2)) ≫ D (.inl 2) := by
  apply fullAtlasPullback_compatible
    (coefficientShearResidueZeroInfinityBoundary_isPullback hπ hm data s hs)
  simpa only [Category.assoc] using
    coefficientShearResidueZeroAtlasCoconeMap_infinity_initial_boundary
      hπ hm data s hs he h3 h4 h6next hc C

/-- Reversing the complete initial/infinity overlap gives the same original cocone equation. -/
theorem coefficientShearResidueZeroAtlasCoconeMap_initial_infinity_pullback :
    pullback.fst (atlas (.inl 2)) (atlas (.inl 0)) ≫ D (.inl 2) =
      pullback.snd (atlas (.inl 2)) (atlas (.inl 0)) ≫ D (.inl 0) := by
  apply (cancel_epi (pullbackSymmetry (atlas (.inl 0)) (atlas (.inl 2))).hom).mp
  simpa only [pullbackSymmetry_hom_comp_fst_assoc, pullbackSymmetry_hom_comp_snd_assoc]
    using (coefficientShearResidueZeroAtlasCoconeMap_infinity_initial_pullback
      hπ hm data s hs he h3 h4 h6next hc C).symm

end FLT.Mazur.WeierstrassDividedDepth
