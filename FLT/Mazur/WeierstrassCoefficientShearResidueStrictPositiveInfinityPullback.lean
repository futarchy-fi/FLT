/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearInitialInfinityParameter
public import FLT.Mazur.WeierstrassCoefficientShearResidueStrictPositiveInitialPullbacks
import all FLT.Mazur.WeierstrassCoefficientShearResidueStrictInitialDescent
import all FLT.Mazur.WeierstrassCoefficientShearResidueStrictPositiveAtlasMaps

/-!
# The full original initial and infinity cocone compatibility

The entire shifted boundary receives the same exterior summand from both
actual chart maps, and hence so does their full categorical pullback.
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

local notation "d" => data ⟨0, Nat.zero_lt_succ n⟩
local notation "ini" => nodalDepth_tangent_linear_zero hπ hm d (by dsimp; omega) h3 h4
local notation "hscale" => nodalDepth_tangent_scale_zero (W := W) hm hstart
local notation "hr" => residueTangentEquation_root W
local notation "U" => rootShearCurve (W.map (algebraMap R Q)) r
local notation "c" => algebraMap R Q (d).b6
local notation "P" => Localization.Away
  (slopePolynomial (U).a₁ * (Polynomial.X + Polynomial.C r))
local notation "p" => Spec.map (CommRingCat.ofHom (algebraMap (Polynomial Q) P))
local notation "E" => coefficientShearInitialEquationIso data Q r (s + 1) hs
  hscale (ini).1 (ini).2 hr
local notation "b" => coefficientShearInitialInfinitySlope hπ data Q r (s + 1) hs
  hscale (ini).1 (ini).2 hr

/-- Both actual cocone maps agree on the whole original shifted infinity boundary. -/
theorem coefficientShearResidueStrictPositiveAtlasCoconeMap_initial_infinity_boundary :
    b ≫ D (.inl 0) = p ≫ fiberIncidenceImmersion (U).a₁ c ≫ (E).hom ≫ D (.inl 2) := by
  rw [coefficientShearResidueStrictPositiveAtlasCoconeMap_infinity,
    coefficientShearResidueStrictPositiveAtlasCoconeMap_initial,
    coefficientShearResidueStrictInitialDesc_incidence,
    coefficientShearResidueStrictInfinityCoconeDesc]
  rw [coefficientShearInitialInfinitySlope_parameter_assoc
    hπ data (s + 1) hs hstart (nodalDepth_residue_uniformizer hm)
    hscale (ini).1 (ini).2 a ha]

/-- The complete infinity/initial pullback satisfies the original cocone gluing equation. -/
theorem coefficientShearResidueStrictPositiveAtlasCoconeMap_infinity_initial_pullback :
    pullback.fst (atlas (.inl 0)) (atlas (.inl 2)) ≫ D (.inl 0) =
      pullback.snd (atlas (.inl 0)) (atlas (.inl 2)) ≫ D (.inl 2) := by
  apply fullAtlasPullback_compatible
    (coefficientShearInitialInfinity_isPullback hπ data Q r (s + 1) hs
      hscale (ini).1 (ini).2 hr)
  simpa only [Category.assoc] using
    coefficientShearResidueStrictPositiveAtlasCoconeMap_initial_infinity_boundary
      hπ hm data s hs hk hstart h3 h4 h6 hc C

/-- Reversing the full initial/infinity intersection preserves the cocone equation. -/
theorem coefficientShearResidueStrictPositiveAtlasCoconeMap_initial_infinity_pullback :
    pullback.fst (atlas (.inl 2)) (atlas (.inl 0)) ≫ D (.inl 2) =
      pullback.snd (atlas (.inl 2)) (atlas (.inl 0)) ≫ D (.inl 0) := by
  apply (cancel_epi (pullbackSymmetry (atlas (.inl 0)) (atlas (.inl 2))).hom).mp
  simpa only [pullbackSymmetry_hom_comp_fst_assoc, pullbackSymmetry_hom_comp_snd_assoc]
    using (coefficientShearResidueStrictPositiveAtlasCoconeMap_infinity_initial_pullback
      hπ hm data s hs hk hstart h3 h4 h6 hc C).symm

end FLT.Mazur.WeierstrassDividedDepth
