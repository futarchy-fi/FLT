/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearResidueStrictZeroAtlasMaps
public import FLT.Mazur.WeierstrassCoefficientShearScaleOneTerminalNodeBoundaryDescent
public import FLT.Mazur.WeierstrassCoefficientShearScaleOneTerminalNodeAtlasPullback
import all FLT.Mazur.WeierstrassCoefficientShearResidueStrictZeroAtlasMaps
import all FLT.Mazur.WeierstrassCoefficientShearResidueStrictZeroFirstCoconeDescent
import all FLT.Mazur.WeierstrassCoefficientShearRetainedScaleOneZeroDescent
import all FLT.Mazur.WeierstrassCoefficientShearRetainedEquationDescent

/-!
# The full strict length-three terminal atlas pullback

The explicit strict terminal boundary exhausts the scheme-theoretic atlas intersection,
so its compatibility gives the required gluing equation on the full pullback.
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
  (hs : 0 + 1 ≤ n) (hk : 2 * (0 + (0 + 1)) < depth)
  (h3 : W.a₃ ∈ maximalIdeal R ^ (depth + 1))
  (h4 : W.a₄ ∈ maximalIdeal R ^ (depth + 1))
  (h6 : W.a₆ ∈ maximalIdeal R ^ depth)
  (hc : IsUnit W.c₄)
local notation "V" => W.map (residue R)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial V)
local notation "r" => AdjoinRoot.root (nodeTangentPolynomial V)
variable [Fact (Irreducible (nodeTangentPolynomial (W.map (residue R))))]
open WeierstrassModificationX WeierstrassSuccessiveX WeierstrassDilatation
local notation "d" => data ⟨0 + 1, Nat.lt_succ_of_le hs⟩
local notation "a" => residueTangentComponentUnit W h3 h4 hc
local notation "ha" => residueTangentComponentUnit_val W h3 h4 hc
variable (C : PushoutCocone (PolygonPinching.toComponents
    (AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))) (2 * 0 + 3) (by omega))
  (PolygonPinching.toNodes
    (AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))) (2 * 0 + 3)))
local notation "F" => PolygonCyclicPushout.inputComponent Q (2 * 0 + 3) C.inl
local notation "w" => fun i => by
  simpa only [PolygonCyclicAtlas.next_eq_rotate] using
    PolygonCyclicPushout.input_condition Q (2 * 0 + 3) (by omega) C.inl C.inr C.condition i

local notation "lin" => nodalDepth_tangent_linear_zero hπ hm d (Nat.le_of_lt hk) h3 h4
local notation "g6" => nodalDepth_tangent_constant_zero hπ hm d hk h6
local notation "hp" => residueTangentEquation_zero W π
  (hm ▸ Ideal.mem_span_singleton_self π)
local notation "hr" => residueTangentEquation_root W
local notation "hscale" => show algebraMap R Q (π ^ (0 + 0)) = 1 from by simp
local notation "U" => rootShearCurve (W.map (algebraMap R Q)) r
local notation "c" => algebraMap R Q (d).b6
local notation "h2" => coefficientShear_a₂_zero W Q r hr
local notation "hsNext" => show algebraMap R Q (π ^ (0 + (0 + 1))) = 0 from by
  rw [← Nat.add_assoc, pow_succ, map_mul, hp, mul_zero]
local notation "L" => coefficientShearTerminalEquationIso
  data Q r (0 + 1) hs hsNext (lin).1 (lin).2 g6 hr a ha
local notation "I" => coefficientShearRetainedScaleOneTensorIso data Q r (0 + 1) hs
  ⟨0, Nat.lt_succ_self 0⟩
local notation "ψ" => tensorShearScaleOneTerminalNodeConicMap W π (0 + 0)
  (d).b3 (d).b4 (d).b6 Q r hscale hp (lin).1 (lin).2 hr g6 a ha
local notation "b" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom ψ))
local notation "inc" => PrincipalOpenTransport.inclusion (conicT (U).a₁ c)
local notation "T" => tensorShearScaleOneConicImmersion W (π ^ (0 + 0)) π
  (d).b3 (d).b4 (d).b6 Q r hscale hp (lin).1 (lin).2 hr
local notation "ρ" => ProjectiveLine.endpointReversal Q
local notation "D" => coefficientShearResidueStrictZeroAtlasCoconeMap
  hπ hm data 0 hs hk h3 h4 h6 hc C

local notation "A" => coefficientShearAtlasMap hπ data Q r (0 + 1) hs
local notation "last" => Sum.inr (Fin.mk 0 (Nat.lt_succ_self 0))
local notation "P" => coefficientShearScaleOneTerminalNodeAtlasPullbackIso
  hπ data Q r 0 hs hscale hp (lin).1 (lin).2 g6 hr a ha

local notation "hu" => Eq.mp (congrArg IsUnit ha) (Units.isUnit a)

omit [IsBezout R] in
/-- The whole last conic receives the two independent terminal component maps. -/
theorem coefficientShearResidueStrictZeroAtlasCoconeMap_lengthThree_conic :
    T ≫ (I).inv ≫ D last =
      conicZeroProjectiveDesc (U).a₁ c hu g6
        (ρ ≫ F ⟨0 + 1, by omega⟩) (F ⟨2 * 0 + 2 - 0, by omega⟩) := by
  rw [coefficientShearResidueStrictZeroAtlasCoconeMap]
  change T ≫ (I).inv ≫ coefficientShearResidueStrictZeroFirstCoconeDesc
    hπ hm data 0 hs hk h3 h4 h6 hc C = _
  rw [coefficientShearResidueStrictZeroFirstCoconeDesc,
    coefficientShearRetainedScaleOneZeroDesc]
  exact coefficientShearRetainedScaleOneDesc_conic
    data Q r 1 hs ⟨0, by decide⟩ hscale hp (lin).1 (lin).2 hr hu _ _ _ _

omit [IsBezout R] in
/-- The complete last conic and divided node agree on their full original boundary. -/
theorem coefficientShearResidueStrictZeroAtlasCoconeMap_lengthThree_boundary :
    inc ≫ T ≫ (I).inv ≫ D last =
      b ≫ (L).hom ≫ D (.inl 1) := by
  rw [coefficientShearResidueStrictZeroAtlasCoconeMap_lengthThree_conic]
  refine coefficientShearScaleOneTerminalNodeBoundary_desc
    W π (0 + 0) (d).b3 (d).b4 (d).b6 Q r hscale hp (lin).1 (lin).2 hr g6 a ha
    (ρ ≫ F ⟨0 + 1, by omega⟩) (F ⟨2 * 0 + 2 - 0, by omega⟩)
    ((L).hom ≫ D (.inl 1)) ?_ ?_
  · rw [ProjectiveLine.right_endpointReversal_assoc, ← Category.assoc]
    change coefficientShearTerminalEquationSecond
      data Q r (0 + 1) hs hsNext (lin).1 (lin).2 g6 hr a ha ≫ D (.inl 1) = _
    rw [coefficientShearResidueStrictZeroAtlasCoconeMap_divided,
      coefficientShearResidueStrictDividedDesc_second]
  · rw [← Category.assoc]
    change coefficientShearTerminalEquationFirst
      data Q r (0 + 1) hs hsNext (lin).1 (lin).2 g6 hr a ha ≫ D (.inl 1) = _
    rw [coefficientShearResidueStrictZeroAtlasCoconeMap_divided,
      coefficientShearResidueStrictDividedDesc_first]

/-- The entire terminal node/retained pullback satisfies the strict cocone gluing equation. -/
theorem coefficientShearResidueStrictZeroAtlasCoconeMap_lengthThree_pullback :
    pullback.fst (A (.inl 1)) (A last) ≫ D (.inl 1) =
      pullback.snd (A (.inl 1)) (A last) ≫ D last := by
  apply (cancel_epi (P).hom).mp
  simp only [← Category.assoc, coefficientShearScaleOneTerminalNodeAtlasPullbackIso_fst,
    coefficientShearScaleOneTerminalNodeAtlasPullbackIso_snd]
  simpa only [Category.assoc] using
    (coefficientShearResidueStrictZeroAtlasCoconeMap_lengthThree_boundary
      hπ hm data hs hk h3 h4 h6 hc C).symm

end FLT.Mazur.WeierstrassDividedDepth
