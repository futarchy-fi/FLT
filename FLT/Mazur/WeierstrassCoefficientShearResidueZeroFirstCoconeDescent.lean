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
# The first start-zero retained chart receives an arbitrary cyclic cocone

For positive chain length its two original conic branches and the complete
exterior line are supplied by the specified normalization coproduct.
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
  (hspos : 0 < s)
  (h3 : W.a₃ ∈ maximalIdeal R ^ (depth + 1))
  (h4 : W.a₄ ∈ maximalIdeal R ^ (depth + 1))
  (hc : IsUnit W.c₄)
local notation "V" => W.map (residue R)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial V)
local notation "r" => AdjoinRoot.root (nodeTangentPolynomial V)
variable [Fact (Irreducible (nodeTangentPolynomial (W.map (residue R))))]
open WeierstrassModificationX WeierstrassSuccessiveX
local notation "d" => data ⟨1, by omega⟩
local notation "e" => data ⟨2, by omega⟩
local notation "hp" => residueTangentEquation_zero W π
  (hm ▸ Ideal.mem_span_singleton_self π)
local notation "gc" => coefficientShearAdjacent_coefficients hπ d e Q hp
local notation "a" => residueTangentComponentUnit W h3 h4 hc
local notation "ha" => residueTangentComponentUnit_val W h3 h4 hc
local notation "hr" => residueTangentEquation_root W
local notation "hscale" => show algebraMap R Q (π ^ (0 + 0)) = 1 from by simp
local notation "U" => rootShearCurve (W.map (algebraMap R Q)) r
local notation "c" => algebraMap R Q (d).b6
local notation "hu" => Eq.mp (congrArg IsUnit ha) (Units.isUnit a)
local notation "Z" => conicZeroAffineIso c (gc).2.2
local notation "E" => coefficientShearRetainedScaleOneTensorIso
  data Q r (s + 1) hs ⟨0, Nat.zero_lt_succ s⟩
local notation "T" => tensorShearScaleOneConicImmersion W (π ^ (0 + 0)) π
  (Data.b3 d) (Data.b4 d) (Data.b6 d) Q r hscale hp (gc).1 (gc).2.1 hr
local notation "L" => Spec.map (CommRingCat.ofHom (tensorShearScaleOneIncidenceMap W
  (π ^ (0 + 0)) π (Data.b3 d) (Data.b4 d) (Data.b6 d) Q r
  hscale hp (gc).1 (gc).2.1 hr).toRingHom)
local notation "p₁" => (conicFirstParameterIso (U).a₁ c hu).inv ≫
  conicFirstOpenImmersion (U).a₁ c
local notation "p₂" => (conicSecondParameterIso (U).a₁ c hu).inv ≫
  conicSecondOpenImmersion (U).a₁ c
local notation "ρ" => ProjectiveLine.endpointReversal Q
variable (C : PushoutCocone (PolygonPinching.toComponents
    (AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))) (2 * s + 2) (by omega))
  (PolygonPinching.toNodes
    (AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))) (2 * s + 2)))
local notation "F" => PolygonCyclicPushout.inputComponent Q (2 * s + 2) C.inl

/-- A cyclic cocone descends on the full first retained chart, with no initial extra pair. -/
@[irreducible] def coefficientShearResidueZeroFirstCoconeDesc :
    coefficientShearAtlasObject data Q r (s + 1) hs (.inr ⟨0, Nat.zero_lt_succ s⟩) ⟶
      C.pt.left :=
  coefficientShearRetainedScaleOneZeroDesc data Q r (s + 1) hs ⟨0, Nat.zero_lt_succ s⟩
    hscale hp (gc).1 (gc).2.1 hr a ha (gc).2.2
    (ρ ≫ F ⟨1, by omega⟩) (F ⟨2 * s + 1, by omega⟩) (F 0)
    (by
      rw [ProjectiveLine.zero_endpointReversal_assoc]
      have w := PolygonCyclicPushout.input_condition Q (2 * s + 2) (by omega)
        C.inl C.inr C.condition 0
      have hn : finRotate (2 * s + 2) 0 = ⟨1, by omega⟩ := by
        rw [← PolygonCyclicAtlas.next_eq_rotate (2 * s + 2) (by omega)]
        apply Fin.ext
        change 1 % (2 * s + 2) = 1
        exact Nat.mod_eq_of_lt (by omega)
      simpa only [hn] using w.symm)
    (by
      have w := PolygonCyclicPushout.input_condition Q (2 * s + 2) (by omega)
        C.inl C.inr C.condition ⟨2 * s + 1, by omega⟩
      have hn : finRotate (2 * s + 2) ⟨2 * s + 1, by omega⟩ = 0 := by
        rw [← PolygonCyclicAtlas.next_eq_rotate (2 * s + 2) (by omega)]
        apply Fin.ext
        change (2 * s + 1 + 1) % (2 * s + 2) = 0
        rw [show 2 * s + 1 + 1 = 2 * s + 2 by omega, Nat.mod_self]
      simpa only [hn] using w)
local notation "D" => coefficientShearResidueZeroFirstCoconeDesc
  hπ hm data s hs hspos h3 h4 hc C

/-- The full first original branch receives the right chart at cyclic position one. -/
theorem coefficientShearResidueZeroFirstCoconeDesc_first :
    (Z).hom ≫ p₁ ≫ T ≫ (E).inv ≫ D = ProjectiveLine.right Q ≫ F ⟨1, by omega⟩ := by
  rw [coefficientShearResidueZeroFirstCoconeDesc]
  erw [coefficientShearRetainedScaleOneZeroDesc_first
    data Q r (s + 1) hs ⟨0, Nat.zero_lt_succ s⟩
      hscale hp (gc).1 (gc).2.1 hr a ha (gc).2.2, ProjectiveLine.left_endpointReversal_assoc]

/-- The full opposite original branch receives the last cyclic component's left chart. -/
theorem coefficientShearResidueZeroFirstCoconeDesc_second :
    (Z).hom ≫ p₂ ≫ T ≫ (E).inv ≫ D =
      ProjectiveLine.left Q ≫ F ⟨2 * s + 1, by omega⟩ := by
  rw [coefficientShearResidueZeroFirstCoconeDesc]
  erw [coefficientShearRetainedScaleOneZeroDesc_second
    data Q r (s + 1) hs ⟨0, Nat.zero_lt_succ s⟩
      hscale hp (gc).1 (gc).2.1 hr a ha (gc).2.2]

/-- The complete incidence line receives the exterior's full original slope chart. -/
theorem coefficientShearResidueZeroFirstCoconeDesc_exterior :
    L ≫ (E).inv ≫ D = ProjectiveLine.left Q ≫
      (ProjectiveLine.slopeNormalizationIso a).hom ≫ F 0 := by
  rw [coefficientShearResidueZeroFirstCoconeDesc]
  erw [coefficientShearRetainedScaleOneZeroDesc_exterior
    data Q r (s + 1) hs ⟨0, Nat.zero_lt_succ s⟩
      hscale hp (gc).1 (gc).2.1 hr a ha (gc).2.2]
  exact Category.assoc _ _ _

end FLT.Mazur.WeierstrassDividedDepth
