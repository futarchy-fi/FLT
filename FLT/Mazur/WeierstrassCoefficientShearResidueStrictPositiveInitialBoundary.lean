/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearResidueStrictPositiveAtlasMaps
public import FLT.Mazur.WeierstrassCoefficientShearResidueStrictPositiveAtlasLines
public import FLT.Mazur.WeierstrassCoefficientShearInitialBoundaryDescent
public import FLT.Mazur.WeierstrassCoefficientShearInitialTensorConicComparison
import all FLT.Mazur.WeierstrassCoefficientShearResidueStrictInitialDescent
import all FLT.Mazur.WeierstrassCoefficientShearInitialTensorConicComparison
import all FLT.Mazur.WeierstrassCoefficientShearRetainedTensorLineComparison
import all FLT.Mazur.WeierstrassCoefficientShearResidueStrictPositiveAtlasLines
import all FLT.Mazur.WeierstrassCoefficientShearResidueStrictPositiveAtlasMaps
import all FLT.Mazur.WeierstrassCoefficientShearResidueTerminalDescent
import all FLT.Mazur.WeierstrassCoefficientShearResidueInteriorDescent
import all FLT.Mazur.WeierstrassCoefficientShearRetainedEquationDescent

/-!
# The strict positive cocone agrees on the entire initial and first retained overlap

Both full initial branches and first retained lines have the prescribed cyclic
maps, including when the first retained chart is also final.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]
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

local notation "d" => data ⟨0, Nat.zero_lt_succ n⟩
local notation "e" => data ⟨1, by omega⟩
local notation "ini" => nodalDepth_tangent_linear_zero hπ hm d (by dsimp; omega) h3 h4
local notation "lin" => nodalDepth_tangent_linear_zero hπ hm e (by dsimp; omega) h3 h4
local notation "g6" => nodalDepth_tangent_constant_zero hπ hm d (by dsimp; omega) h6
local notation "hp" => residueTangentEquation_zero W π
  (hm ▸ Ideal.mem_span_singleton_self π)
local notation "hr" => residueTangentEquation_root W
local notation "hscale" => nodalDepth_tangent_scale_zero (W := W) hm hstart
local notation "U" => rootShearCurve (W.map (algebraMap R Q)) r
local notation "c" => algebraMap R Q (d).b6
local notation "hu" => Eq.mp (congrArg IsUnit ha) (Units.isUnit a)
local notation "x" => WeierstrassDilatation.x W (π ^ start) (d).b3 (d).b4 (d).b6
local notation "t₀" => WeierstrassModificationX.t W (π ^ start) (d).b3 (d).b4 (d).b6
local notation "u₀" => coord W (π ^ start) π (e).b3 (e).b4 (e).b6 2
local notation "A" => PrincipalOpenTensor.transitionIso Q x t₀
  (WeierstrassModificationX.overlapEquiv W (π ^ start) (d).b3 (d).b4 (d).b6)
local notation "B" => PrincipalOpenTensor.transitionIso Q x u₀ (previousBoundaryEquiv hπ d e)
local notation "ci" => incidenceCoefficientShearIso W (π ^ start)
  (d).b3 (d).b4 (d).b6 Q r
local notation "cj" => successiveCoefficientShearIso W (π ^ start) π
  (e).b3 (e).b4 (e).b6 Q r
local notation "D" => coefficientShearResidueStrictPositiveAtlasCoconeMap
  hπ hm data s hs hk hstart h3 h4 h6 hc C
local notation "ρ" => ProjectiveLine.endpointReversal Q

set_option maxHeartbeats 600000 in
-- Comparing the two indexed tensor presentations exceeds the default elaboration limit.
/-- The actual full initial/first-retained overlap satisfies the cocone equation. -/
theorem coefficientShearResidueStrictPositiveAtlasCoconeMap_initial_boundary :
    (A).inv ≫ PrincipalOpenTensor.inclusion Q t₀ ≫ (ci).inv ≫ D (.inl 2) =
      (B).inv ≫ PrincipalOpenTensor.inclusion Q u₀ ≫ (cj).inv ≫ D (.inr 0) := by
  apply coefficientShearInitialBoundary_desc hπ d e Q r hscale hp (lin).1 (lin).2 hr
    (ini).1 (ini).2 g6 a ha (ρ ≫ F 1) (F ⟨2 * s + 4, by omega⟩)
  · simp only [Category.assoc]
    erw [coefficientShearInitialEquationIso_tensor_conic_assoc
      data Q r (s + 1) hs hscale (ini).1 (ini).2 hr]
    rw [coefficientShearResidueStrictPositiveAtlasCoconeMap_initial,
      ProjectiveLine.left_endpointReversal_assoc]
    simpa only [Category.assoc] using coefficientShearResidueStrictInitialDesc_first
      hπ hm data s hs (Nat.le_of_lt hk) hstart h3 h4 h6 hc F w
  · simp only [Category.assoc]
    erw [coefficientShearInitialEquationIso_tensor_conic_assoc
      data Q r (s + 1) hs hscale (ini).1 (ini).2 hr]
    rw [coefficientShearResidueStrictPositiveAtlasCoconeMap_initial]
    simpa only [Category.assoc] using coefficientShearResidueStrictInitialDesc_second
      hπ hm data s hs (Nat.le_of_lt hk) hstart h3 h4 h6 hc F w
  · rw [← Category.assoc]
    erw [coefficientShearRetainedEquationIso_tensor_line data Q r (s + 1) hs 0]
    rw [Category.assoc, coefficientShearResidueStrictPositiveAtlasCoconeMap_first_line,
      ProjectiveLine.right_endpointReversal_assoc]
    rfl
  · rw [← Category.assoc]
    erw [coefficientShearRetainedEquationIso_tensor_line data Q r (s + 1) hs 0]
    rw [Category.assoc, coefficientShearResidueStrictPositiveAtlasCoconeMap_second_line]
    rfl

end FLT.Mazur.WeierstrassDividedDepth
