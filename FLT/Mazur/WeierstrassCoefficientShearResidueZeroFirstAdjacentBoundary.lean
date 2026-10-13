/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearResidueZeroAtlasCoconeMaps
public import FLT.Mazur.WeierstrassCoefficientShearResidueZeroAtlasLines
import all FLT.Mazur.WeierstrassCoefficientShearResidueZeroAtlasLines
public import FLT.Mazur.WeierstrassCoefficientShearScaleOneAdjacentBoundaryDescent
import all FLT.Mazur.WeierstrassCoefficientShearRetainedScaleOneZeroDescent
import all FLT.Mazur.WeierstrassCoefficientShearRetainedScaleOneDescent
import all FLT.Mazur.WeierstrassCoefficientShearResidueZeroFirstCoconeDescent
import all FLT.Mazur.WeierstrassCoefficientShearRetainedTensorLineComparison
import all FLT.Mazur.WeierstrassCoefficientShearResidueZeroAtlasCoconeMaps
import all FLT.Mazur.WeierstrassCoefficientShearResidueZeroRetainedCoconeMaps
import all FLT.Mazur.WeierstrassCoefficientShearResidueZeroTerminalDescent
import all FLT.Mazur.WeierstrassCoefficientShearResidueZeroInteriorDescent
import all FLT.Mazur.WeierstrassCoefficientShearRetainedEquationDescent

/-!
# The full first adjacent boundary of the original start-zero cocone

The full old conic descent and the next whole tensor equation agree on their
entire original incidence boundary, including when the next chart is final.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0)
  (hm : maximalIdeal R = Ideal.span {π}) {n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (s : ℕ) (hs : s + 1 ≤ n) (he : 2 * (0 + (s + 1)) = depth)
  (h3 : W.a₃ ∈ maximalIdeal R ^ (depth + 1))
  (h4 : W.a₄ ∈ maximalIdeal R ^ (depth + 1))
  (h6next : W.a₆ ∉ maximalIdeal R ^ (depth + 1)) (hc : IsUnit W.c₄)
local notation "V" => W.map (residue R)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial V)
local notation "r" => AdjoinRoot.root (nodeTangentPolynomial V)
variable [Fact (Irreducible (nodeTangentPolynomial (W.map (residue R))))]
open WeierstrassModificationX WeierstrassSuccessiveX WeierstrassDilatation
local notation "a" => residueTangentComponentUnit W h3 h4 hc
local notation "ha" => residueTangentComponentUnit_val W h3 h4 hc
variable (C : PushoutCocone (PolygonPinching.toComponents
    (AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))) (2 * s + 2) (by omega))
  (PolygonPinching.toNodes
    (AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))) (2 * s + 2)))
local notation "F" => PolygonCyclicPushout.inputComponent Q (2 * s + 2) C.inl
local notation "w" => fun i => by
  simpa only [PolygonCyclicAtlas.next_eq_rotate] using
    PolygonCyclicPushout.input_condition Q (2 * s + 2) (by omega) C.inl C.inr C.condition i

variable (hspos : 0 < s)
local notation "d" => data ⟨0 + 1, by omega⟩
local notation "e" => data ⟨0 + 2, by omega⟩
local notation "hp" => residueTangentEquation_zero W π
  (hm ▸ Ideal.mem_span_singleton_self π)
local notation "hr" => residueTangentEquation_root W
local notation "hscale" => show algebraMap R Q (π ^ (0 + 0)) = 1 from by simp
local notation "gc" => coefficientShearAdjacent_coefficients hπ d e Q hp
local notation "lin" => nodalDepth_tangent_linear_zero hπ hm e (show
  2 * (0 + (0 + 2)) ≤ depth from by omega) h3 h4
local notation "U" => rootShearCurve (W.map (algebraMap R Q)) r
local notation "c" => algebraMap R Q (d).b6
local notation "h2" => coefficientShear_a₂_zero W Q r hr
local notation "hu" => Eq.mp (congrArg IsUnit ha) (Units.isUnit a)
local notation "I" => coefficientShearRetainedScaleOneTensorIso data Q r (s + 1) hs
  ⟨0, Nat.zero_lt_succ s⟩
local notation "T" => tensorShearScaleOneConicImmersion W (π ^ (0 + 0)) π
  (d).b3 (d).b4 (d).b6 Q r hscale hp (gc).1 (gc).2.1 hr
local notation "ρ" => ProjectiveLine.endpointReversal Q
local notation "D" => coefficientShearResidueZeroAtlasCoconeMap
  hπ hm data s hs he h3 h4 h6next hc C
local notation "ci" => successiveCoefficientShearIso W (π ^ (0 + 0 + 1)) π
  (e).b3 (e).b4 (e).b6 Q r
local notation "N" => coefficientShearScaleOneAdjacentConicToNext
  (k := 0 + 0) hπ d e Q r hscale hp hr
local notation "inc" => PrincipalOpenTransport.inclusion (conicT (U).a₁ c)
local notation "next" => (⟨0 + 1, by omega⟩ : Fin (s + 1))

/-- The entire old conic receives its actual pair of cyclic component maps. -/
theorem coefficientShearResidueZeroAtlasCoconeMap_first_conic :
    T ≫ (I).inv ≫ D (.inr (⟨0, Nat.zero_lt_succ s⟩ : Fin (s + 1))) =
      conicZeroProjectiveDesc (U).a₁ c hu (gc).2.2
        (ρ ≫ F ⟨0 + 1, by omega⟩) (F ⟨2 * s + 1, by omega⟩) := by
  rw [coefficientShearResidueZeroAtlasCoconeMap_retained,
    coefficientShearResidueZeroRetainedCoconeMap_first hπ hm data s hs he h3 h4 h6next hc C
      hspos, coefficientShearResidueZeroFirstCoconeDesc,
    coefficientShearRetainedScaleOneZeroDesc]
  exact coefficientShearRetainedScaleOneDesc_conic
    data Q r (s + 1) hs ⟨0, Nat.zero_lt_succ s⟩ hscale hp (gc).1 (gc).2.1 hr hu _ _ _ _

/-- The actual old and next cocone maps agree on the entire adjacent boundary. -/
theorem coefficientShearResidueZeroAtlasCoconeMap_first_adjacent_boundary :
    inc ≫ T ≫ (I).inv ≫ D (.inr (⟨0, Nat.zero_lt_succ s⟩ : Fin (s + 1))) =
      N ≫ (ci).inv ≫ D (.inr next) := by
  have hconic := congrArg (fun f => inc ≫ f)
    (coefficientShearResidueZeroAtlasCoconeMap_first_conic
      hπ hm data s hs he h3 h4 h6next hc C hspos)
  refine hconic.trans ?_
  refine coefficientShearScaleOneAdjacentBoundary_desc (k := 0 + 0)
    hπ d e Q r hscale hp (lin).1 (lin).2 hr a ha
    (ρ ≫ F ⟨1, by omega⟩) (F ⟨2 * s + 1, by omega⟩)
    ((ci).inv ≫ D (.inr next)) ?_ ?_
  · rw [← Category.assoc]
    erw [coefficientShearRetainedEquationIso_tensor_line
      data Q r (s + 1) hs next]
    rw [Category.assoc, coefficientShearResidueZeroAtlasCoconeMap_first_line
      hπ hm data s hs he h3 h4 h6next hc C next (by dsimp; omega),
      ProjectiveLine.right_endpointReversal_assoc]
  · rw [← Category.assoc]
    erw [coefficientShearRetainedEquationIso_tensor_line
      data Q r (s + 1) hs next]
    rw [Category.assoc, coefficientShearResidueZeroAtlasCoconeMap_second_line
      hπ hm data s hs he h3 h4 h6next hc C next (by dsimp; omega)]
    congr 3

end FLT.Mazur.WeierstrassDividedDepth
