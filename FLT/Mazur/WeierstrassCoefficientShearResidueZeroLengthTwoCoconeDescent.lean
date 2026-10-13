/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearRetainedScaleOneEqualityDescent
public import FLT.Mazur.WeierstrassResidueTangentComponentData
public import FLT.Mazur.PolygonCyclicPushout
import all FLT.Mazur.WeierstrassCoefficientShearRetainedScaleOneEqualityDescent

/-!
# The two-component start-zero equality cocone on its full retained chart

The original nonzero conic and exterior provide compatible maps without
replacing the conic or introducing an extra initial pair.
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
  (hs : 0 + 1 ≤ n) (he : 2 * (0 + (0 + 1)) = depth)
  (h3 : W.a₃ ∈ maximalIdeal R ^ (depth + 1))
  (h4 : W.a₄ ∈ maximalIdeal R ^ (depth + 1))
  (h6next : W.a₆ ∉ maximalIdeal R ^ (depth + 1)) (hc : IsUnit W.c₄)
local notation "V" => W.map (residue R)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial V)
local notation "r" => AdjoinRoot.root (nodeTangentPolynomial V)
variable [Fact (Irreducible (nodeTangentPolynomial (W.map (residue R))))]
open WeierstrassModificationX WeierstrassSuccessiveX
local notation "d" => data ⟨1, Nat.lt_succ_of_le hs⟩
local notation "lin" => nodalDepth_tangent_linear_zero hπ hm d (Nat.le_of_eq he) h3 h4
local notation "cunit" => nodalDepth_tangent_constant_isUnit hm d he h6next
local notation "hp" => residueTangentEquation_zero W π
  (hm ▸ Ideal.mem_span_singleton_self π)
local notation "a" => residueTangentComponentUnit W h3 h4 hc
local notation "ha" => residueTangentComponentUnit_val W h3 h4 hc
local notation "hr" => residueTangentEquation_root W
local notation "hscale" => show algebraMap R Q (π ^ (0 + 0)) = 1 from by simp
local notation "E" => coefficientShearRetainedScaleOneTensorIso data Q r 1 hs ⟨0, by decide⟩
local notation "T" => tensorShearScaleOneConicImmersion W (π ^ (0 + 0)) π
  (Data.b3 d) (Data.b4 d) (Data.b6 d) Q r hscale hp (lin).1 (lin).2 hr
local notation "L" => Spec.map (CommRingCat.ofHom (tensorShearScaleOneIncidenceMap W
  (π ^ (0 + 0)) π (Data.b3 d) (Data.b4 d) (Data.b6 d) Q r
  hscale hp (lin).1 (lin).2 hr).toRingHom)
local notation "q" => coefficientShearScaleOneEqualityConicParameter
  data Q r 0 hs hp (lin).1 (lin).2 cunit hr a ha
local notation "ρ" => ProjectiveLine.endpointReversal Q
variable (C : PushoutCocone (PolygonPinching.toComponents
    (AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))) 2 (by decide))
  (PolygonPinching.toNodes (AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))) 2))
local notation "F" => PolygonCyclicPushout.inputComponent Q 2 C.inl

/-- Any two-component cyclic cocone descends to the full actual retained equation. -/
@[irreducible] def coefficientShearResidueZeroLengthTwoCoconeDesc :
    coefficientShearAtlasObject data Q r 1 hs (.inr ⟨0, by decide⟩) ⟶ C.pt.left :=
  coefficientShearRetainedScaleOneEqualityDesc data Q r 0 hs hscale hp (lin).1 (lin).2 hr
    a ha cunit (ρ ≫ F 1) (F 0)
    (by
      rw [ProjectiveLine.zero_endpointReversal_assoc]
      have w := PolygonCyclicPushout.input_condition Q 2 (by decide)
        C.inl C.inr C.condition 0
      simpa only [show finRotate 2 0 = 1 from rfl] using w.symm)
    (by
      rw [ProjectiveLine.infinity_endpointReversal_assoc]
      have w := PolygonCyclicPushout.input_condition Q 2 (by decide)
        C.inl C.inr C.condition 1
      simpa only [show finRotate 2 1 = 0 from rfl] using w)
local notation "D" => coefficientShearResidueZeroLengthTwoCoconeDesc
  hπ hm data hs he h3 h4 h6next hc C

/-- The full original conic receives the reversed equality component at position one. -/
theorem coefficientShearResidueZeroLengthTwoCoconeDesc_conic :
    T ≫ (E).inv ≫ D = q ≫ ρ ≫ F 1 := by
  rw [coefficientShearResidueZeroLengthTwoCoconeDesc]
  erw [coefficientShearRetainedScaleOneEqualityDesc_conic]

/-- The entire original incidence line receives the exterior's actual slope chart. -/
theorem coefficientShearResidueZeroLengthTwoCoconeDesc_exterior :
    L ≫ (E).inv ≫ D = ProjectiveLine.left Q ≫
      (ProjectiveLine.slopeNormalizationIso a).hom ≫ F 0 := by
  rw [coefficientShearResidueZeroLengthTwoCoconeDesc]
  erw [coefficientShearRetainedScaleOneEqualityDesc_exterior]
  exact Category.assoc _ _ _

end FLT.Mazur.WeierstrassDividedDepth
