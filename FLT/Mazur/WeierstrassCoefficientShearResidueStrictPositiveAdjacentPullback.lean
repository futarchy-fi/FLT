/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearResidueAtlasAdjacentPullback
public import FLT.Mazur.WeierstrassCoefficientShearResidueStrictPositiveAdjacentBoundary
public import FLT.Mazur.WeierstrassCoefficientShearAdjacentAtlasPullback
import all FLT.Mazur.WeierstrassCoefficientShearAdjacentAtlasPullback
import all FLT.Mazur.WeierstrassCoefficientShearResidueStrictPositiveAdjacentBoundary
public import FLT.Mazur.WeierstrassCoefficientShearAdjacentBoundaryDescent
import all FLT.Mazur.WeierstrassCoefficientShearRetainedZeroDescent
import all FLT.Mazur.WeierstrassCoefficientShearResidueStrictPositiveAtlasMaps
import all FLT.Mazur.WeierstrassCoefficientShearResidueTerminalDescent
import all FLT.Mazur.WeierstrassCoefficientShearResidueInteriorDescent
import all FLT.Mazur.WeierstrassCoefficientShearRetainedEquationDescent

/-!
# Compatibility on the full actual adjacent atlas pullbacks

Every adjacent pair of retained charts satisfies the original cocone gluing
equation, in both orders and including the final retained chart.
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
local notation "F" => PolygonCyclicPushout.inputComponent Q (2 * s + 5) C.inl
local notation "w" => fun i => by
  simpa only [PolygonCyclicAtlas.next_eq_rotate] using
    PolygonCyclicPushout.input_condition Q (2 * s + 5) (by omega) C.inl C.inr C.condition i

variable (j : Fin s)
local notation "d" => data ⟨j.val + 1, by omega⟩
local notation "e" => data ⟨j.val + 2, by omega⟩
local notation "hp" => residueTangentEquation_zero W π
  (hm ▸ Ideal.mem_span_singleton_self π)
local notation "hr" => residueTangentEquation_root W
local notation "hscale" => nodalDepth_tangent_scale_zero (W := W) hm
  (show 0 < start + j.val from by omega)
local notation "gc" => coefficientShearAdjacent_coefficients hπ d e Q hp
local notation "lin" => nodalDepth_tangent_linear_zero hπ hm e (show
  2 * (start + (j.val + 2)) ≤ depth from by omega) h3 h4
local notation "U" => rootShearCurve (W.map (algebraMap R Q)) r
local notation "c" => algebraMap R Q (d).b6
local notation "h2" => coefficientShear_a₂_zero W Q r hr
local notation "hu" => Eq.mp (congrArg IsUnit ha) (Units.isUnit a)
local notation "I" => coefficientShearRetainedEquationIso data Q r (s + 1) hs
  j.castSucc hscale hp (gc).1 (gc).2.1
local notation "ρ" => ProjectiveLine.endpointReversal Q
local notation "D" => coefficientShearResidueStrictPositiveAtlasCoconeMap
  hπ hm data s hs hk hstart h3 h4 h6 hc C
local notation "ci" => successiveCoefficientShearIso W (π ^ (start + (j.val + 1))) π
  (e).b3 (e).b4 (e).b6 Q r
local notation "N" => coefficientShearAdjacentConicToNext hπ d e Q r hscale hp hr
local notation "inc" => PrincipalOpenTransport.inclusion (conicT (U).a₁ c)
local notation "next" => (⟨j.val + 1, by omega⟩ : Fin (s + 1))

local notation "A" => coefficientShearAtlasMap hπ data Q r (s + 1) hs

/-- The full adjacent boundary square at the actual strict depth. -/
theorem coefficientShearResidueStrictPositiveAtlasAdjacent_isPullback :
    IsPullback (inc ≫ middleConicImmersion U c h2 ≫ (I).hom)
      (N ≫ (ci).inv) (A (.inr j.castSucc)) (A (.inr next)) := by
  exact coefficientShearAdjacentAtlas_atDepth_isPullback
    hπ data Q r (s + 1) hs j.val (by omega) hscale hp hr

/-- The actual cocone maps agree on every full adjacent scheme-theoretic intersection. -/
theorem coefficientShearResidueStrictPositiveAtlasCoconeMap_adjacent_pullback :
    pullback.fst (A (.inr j.castSucc)) (A (.inr next)) ≫ D (.inr j.castSucc) =
      pullback.snd (A (.inr j.castSucc)) (A (.inr next)) ≫ D (.inr next) := by
  apply fullAtlasPullback_compatible
    (coefficientShearResidueStrictPositiveAtlasAdjacent_isPullback
      (depth := depth) hπ hm data s hs hstart j)
  simpa only [Category.assoc] using
    coefficientShearResidueStrictPositiveAtlasCoconeMap_adjacent_boundary
      hπ hm data s hs hk hstart h3 h4 h6 hc C j

/-- The reversed adjacent pair satisfies the same full gluing equation. -/
theorem coefficientShearResidueStrictPositiveAtlasCoconeMap_adjacent_pullback_symm :
    pullback.fst (A (.inr next)) (A (.inr j.castSucc)) ≫ D (.inr next) =
      pullback.snd (A (.inr next)) (A (.inr j.castSucc)) ≫ D (.inr j.castSucc) := by
  apply (cancel_epi (pullbackSymmetry (A (.inr j.castSucc)) (A (.inr next))).hom).mp
  simpa only [pullbackSymmetry_hom_comp_fst_assoc, pullbackSymmetry_hom_comp_snd_assoc]
    using (coefficientShearResidueStrictPositiveAtlasCoconeMap_adjacent_pullback
      hπ hm data s hs hk hstart h3 h4 h6 hc C j).symm

end FLT.Mazur.WeierstrassDividedDepth
