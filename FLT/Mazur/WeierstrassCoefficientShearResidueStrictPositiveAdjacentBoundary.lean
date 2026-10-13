/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearResidueStrictPositiveAtlasMaps
public import FLT.Mazur.WeierstrassCoefficientShearResidueStrictPositiveAtlasLines
import all FLT.Mazur.WeierstrassCoefficientShearResidueStrictPositiveAtlasLines
public import FLT.Mazur.WeierstrassCoefficientShearAdjacentBoundaryDescent
import all FLT.Mazur.WeierstrassCoefficientShearRetainedZeroDescent
import all FLT.Mazur.WeierstrassCoefficientShearRetainedTensorLineComparison
import all FLT.Mazur.WeierstrassCoefficientShearResidueStrictPositiveAtlasMaps
import all FLT.Mazur.WeierstrassCoefficientShearResidueTerminalDescent
import all FLT.Mazur.WeierstrassCoefficientShearResidueStrictPositiveRetainedDescent
import all FLT.Mazur.WeierstrassCoefficientShearRetainedEquationDescent

/-!
# Adjacent boundary compatibility of the strict positive residue cocone

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

/-- The entire old conic receives its actual pair of cyclic component maps. -/
theorem coefficientShearResidueStrictPositiveAtlasCoconeMap_interior_conic :
    middleConicImmersion U c h2 ≫ (I).hom ≫ D (.inr j.castSucc) =
      conicZeroProjectiveDesc (U).a₁ c hu (gc).2.2
        (ρ ≫ F ⟨j.val + 2, by omega⟩) (F ⟨2 * s + 3 - j.val, by omega⟩) := by
  rw [coefficientShearResidueStrictPositiveAtlasCoconeMap_retained,
    coefficientShearResidueStrictPositiveRetainedDesc,
    coefficientShearRetainedZeroDesc]
  erw [coefficientShearRetainedEquationDesc_conic
    data Q r (s + 1) hs j.castSucc hscale hp (gc).1 (gc).2.1 hr hu]
  rfl

/-- The actual old and next cocone maps agree on the entire adjacent boundary. -/
theorem coefficientShearResidueStrictPositiveAtlasCoconeMap_adjacent_boundary :
    inc ≫ middleConicImmersion U c h2 ≫ (I).hom ≫ D (.inr j.castSucc) =
      N ≫ (ci).inv ≫ D (.inr next) := by
  rw [coefficientShearResidueStrictPositiveAtlasCoconeMap_interior_conic]
  apply coefficientShearAdjacentBoundary_desc hπ d e Q r hscale hp (lin).1 (lin).2 hr a ha
  · rw [← Category.assoc]
    erw [coefficientShearRetainedEquationIso_tensor_line
      data Q r (s + 1) hs next]
    rw [Category.assoc, coefficientShearResidueStrictPositiveAtlasCoconeMap_first_line,
      ProjectiveLine.right_endpointReversal_assoc]
  · rw [← Category.assoc]
    erw [coefficientShearRetainedEquationIso_tensor_line
      data Q r (s + 1) hs next]
    rw [Category.assoc, coefficientShearResidueStrictPositiveAtlasCoconeMap_second_line]
    congr 3
    apply Fin.ext
    change 2 * s + 4 - (j.val + 1) = 2 * s + 3 - j.val
    omega

end FLT.Mazur.WeierstrassDividedDepth
