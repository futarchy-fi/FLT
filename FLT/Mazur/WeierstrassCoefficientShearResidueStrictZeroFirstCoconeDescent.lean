/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearRetainedScaleOneZeroDescent
public import FLT.Mazur.WeierstrassResidueTangentComponentData
public import FLT.Mazur.WeierstrassCoefficientShearAdjacentLine
public import FLT.Mazur.PolygonCyclicPushout
import all FLT.Mazur.WeierstrassCoefficientShearRetainedScaleOneZeroDescent

/-!
# The first strict-depth chart receives the original odd cyclic cocone

The two full conic branches and the exterior supply the scale-one equation,
including the length-zero cycle where the conic branches are terminal.
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
  (s : ℕ) (hs : s + 1 ≤ n)
  (hk : 2 * (0 + (s + 1)) < depth)
  (h3 : W.a₃ ∈ maximalIdeal R ^ (depth + 1))
  (h4 : W.a₄ ∈ maximalIdeal R ^ (depth + 1))
  (h6 : W.a₆ ∈ maximalIdeal R ^ depth) (hc : IsUnit W.c₄)
local notation "V" => W.map (residue R)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial V)
local notation "r" => AdjoinRoot.root (nodeTangentPolynomial V)
variable [Fact (Irreducible (nodeTangentPolynomial (W.map (residue R))))]
open WeierstrassModificationX WeierstrassSuccessiveX
local notation "d" => data ⟨1, by omega⟩
local notation "hp" => residueTangentEquation_zero W π
  (hm ▸ Ideal.mem_span_singleton_self π)
local notation "lin" => nodalDepth_tangent_linear_zero hπ hm d (by dsimp; omega) h3 h4
local notation "g6" => nodalDepth_tangent_constant_zero hπ hm d (by dsimp; omega) h6
local notation "a" => residueTangentComponentUnit W h3 h4 hc
local notation "ha" => residueTangentComponentUnit_val W h3 h4 hc
local notation "hr" => residueTangentEquation_root W
local notation "hscale" => show algebraMap R Q (π ^ (0 + 0)) = 1 from by simp
local notation "U" => rootShearCurve (W.map (algebraMap R Q)) r
local notation "c" => algebraMap R Q (d).b6
local notation "hu" => Eq.mp (congrArg IsUnit ha) (Units.isUnit a)
local notation "Z" => conicZeroAffineIso c g6
local notation "E" => coefficientShearRetainedScaleOneTensorIso
  data Q r (s + 1) hs ⟨0, Nat.zero_lt_succ s⟩
local notation "T" => tensorShearScaleOneConicImmersion W (π ^ (0 + 0)) π
  (Data.b3 d) (Data.b4 d) (Data.b6 d) Q r hscale hp (lin).1 (lin).2 hr
local notation "L" => Spec.map (CommRingCat.ofHom (tensorShearScaleOneIncidenceMap W
  (π ^ (0 + 0)) π (Data.b3 d) (Data.b4 d) (Data.b6 d) Q r
  hscale hp (lin).1 (lin).2 hr).toRingHom)
local notation "p₁" => (conicFirstParameterIso (U).a₁ c hu).inv ≫
  conicFirstOpenImmersion (U).a₁ c
local notation "p₂" => (conicSecondParameterIso (U).a₁ c hu).inv ≫
  conicSecondOpenImmersion (U).a₁ c
local notation "ρ" => ProjectiveLine.endpointReversal Q
variable (C : PushoutCocone (PolygonPinching.toComponents
    (AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))) (2 * s + 3) (by omega))
  (PolygonPinching.toNodes
    (AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))) (2 * s + 3)))
local notation "F" => PolygonCyclicPushout.inputComponent Q (2 * s + 3) C.inl

/-- A cyclic cocone descends on the full first retained chart, with no initial extra pair. -/
@[irreducible] def coefficientShearResidueStrictZeroFirstCoconeDesc :
    coefficientShearAtlasObject data Q r (s + 1) hs (.inr ⟨0, Nat.zero_lt_succ s⟩) ⟶
      C.pt.left :=
  coefficientShearRetainedScaleOneZeroDesc data Q r (s + 1) hs ⟨0, Nat.zero_lt_succ s⟩
    hscale hp (lin).1 (lin).2 hr a ha g6
    (ρ ≫ F ⟨1, by omega⟩) (F ⟨2 * s + 2, by omega⟩) (F 0)
    (by
      rw [ProjectiveLine.zero_endpointReversal_assoc]
      have w := PolygonCyclicPushout.input_condition Q (2 * s + 3) (by omega)
        C.inl C.inr C.condition 0
      have hn : finRotate (2 * s + 3) 0 = ⟨1, by omega⟩ := by
        rw [← PolygonCyclicAtlas.next_eq_rotate (2 * s + 3) (by omega)]
        apply Fin.ext
        change 1 % (2 * s + 3) = 1
        exact Nat.mod_eq_of_lt (by omega)
      simpa only [hn] using w.symm)
    (by
      have w := PolygonCyclicPushout.input_condition Q (2 * s + 3) (by omega)
        C.inl C.inr C.condition ⟨2 * s + 2, by omega⟩
      have hn : finRotate (2 * s + 3) ⟨2 * s + 2, by omega⟩ = 0 := by
        rw [← PolygonCyclicAtlas.next_eq_rotate (2 * s + 3) (by omega)]
        apply Fin.ext
        change (2 * s + 2 + 1) % (2 * s + 3) = 0
        rw [show 2 * s + 2 + 1 = 2 * s + 3 by omega, Nat.mod_self]
      simpa only [hn] using w)
local notation "D" => coefficientShearResidueStrictZeroFirstCoconeDesc
  hπ hm data s hs hk h3 h4 h6 hc C

/-- The full first original branch receives the right chart at cyclic position one. -/
theorem coefficientShearResidueStrictZeroFirstCoconeDesc_first :
    (Z).hom ≫ p₁ ≫ T ≫ (E).inv ≫ D = ProjectiveLine.right Q ≫ F ⟨1, by omega⟩ := by
  rw [coefficientShearResidueStrictZeroFirstCoconeDesc]
  erw [coefficientShearRetainedScaleOneZeroDesc_first
    data Q r (s + 1) hs ⟨0, Nat.zero_lt_succ s⟩
      hscale hp (lin).1 (lin).2 hr a ha g6, ProjectiveLine.left_endpointReversal_assoc]

/-- The full opposite original branch receives the last cyclic component's left chart. -/
theorem coefficientShearResidueStrictZeroFirstCoconeDesc_second :
    (Z).hom ≫ p₂ ≫ T ≫ (E).inv ≫ D =
      ProjectiveLine.left Q ≫ F ⟨2 * s + 2, by omega⟩ := by
  rw [coefficientShearResidueStrictZeroFirstCoconeDesc]
  erw [coefficientShearRetainedScaleOneZeroDesc_second
    data Q r (s + 1) hs ⟨0, Nat.zero_lt_succ s⟩
      hscale hp (lin).1 (lin).2 hr a ha g6]

/-- The complete incidence line receives the exterior's full original slope chart. -/
theorem coefficientShearResidueStrictZeroFirstCoconeDesc_exterior :
    L ≫ (E).inv ≫ D = ProjectiveLine.left Q ≫
      (ProjectiveLine.slopeNormalizationIso a).hom ≫ F 0 := by
  rw [coefficientShearResidueStrictZeroFirstCoconeDesc]
  erw [coefficientShearRetainedScaleOneZeroDesc_exterior
    data Q r (s + 1) hs ⟨0, Nat.zero_lt_succ s⟩
      hscale hp (lin).1 (lin).2 hr a ha g6]
  exact Category.assoc _ _ _

end FLT.Mazur.WeierstrassDividedDepth
