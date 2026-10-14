/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearResidueStrictZeroAtlasMaps
public import FLT.Mazur.WeierstrassCoefficientShearTerminalNodeBoundaryDescent
public import FLT.Mazur.WeierstrassCoefficientShearTerminalNodeAtlasPullback
import all FLT.Mazur.WeierstrassCoefficientShearResidueStrictZeroAtlasMaps
import all FLT.Mazur.WeierstrassCoefficientShearResidueStrictZeroRetainedDescent
import all FLT.Mazur.WeierstrassCoefficientShearRetainedZeroDescent
import all FLT.Mazur.WeierstrassCoefficientShearRetainedEquationDescent

/-!
# Actual cocone compatibility on the full terminal atlas pullback

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
  (s : ℕ) (hs : s + 1 ≤ n) (hk : 2 * (0 + (s + 1)) < depth)
  (hspos : 0 < s)
  (h3 : W.a₃ ∈ maximalIdeal R ^ (depth + 1))
  (h4 : W.a₄ ∈ maximalIdeal R ^ (depth + 1))
  (h6 : W.a₆ ∈ maximalIdeal R ^ depth)
  (hc : IsUnit W.c₄)
local notation "V" => W.map (residue R)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial V)
local notation "r" => AdjoinRoot.root (nodeTangentPolynomial V)
variable [Fact (Irreducible (nodeTangentPolynomial (W.map (residue R))))]
open WeierstrassModificationX WeierstrassSuccessiveX WeierstrassDilatation
local notation "d" => data ⟨s + 1, Nat.lt_succ_of_le hs⟩
local notation "a" => residueTangentComponentUnit W h3 h4 hc
local notation "ha" => residueTangentComponentUnit_val W h3 h4 hc
variable (C : PushoutCocone (PolygonPinching.toComponents
    (AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))) (2 * s + 3) (by omega))
  (PolygonPinching.toNodes
    (AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))) (2 * s + 3)))
local notation "F" => PolygonCyclicPushout.inputComponent Q (2 * s + 3) C.inl
local notation "w" => fun i => by
  simpa only [PolygonCyclicAtlas.next_eq_rotate] using
    PolygonCyclicPushout.input_condition Q (2 * s + 3) (by omega) C.inl C.inr C.condition i

local notation "lin" => nodalDepth_tangent_linear_zero hπ hm d (Nat.le_of_lt hk) h3 h4
local notation "g6" => nodalDepth_tangent_constant_zero hπ hm d hk h6
local notation "hp" => residueTangentEquation_zero W π
  (hm ▸ Ideal.mem_span_singleton_self π)
local notation "hr" => residueTangentEquation_root W
local notation "hscale" => nodalDepth_tangent_scale_zero (W := W) hm
  (show 0 < 0 + s from by omega)
local notation "U" => rootShearCurve (W.map (algebraMap R Q)) r
local notation "c" => algebraMap R Q (d).b6
local notation "h2" => coefficientShear_a₂_zero W Q r hr
local notation "hsNext" => show algebraMap R Q (π ^ (0 + (s + 1))) = 0 from by
  rw [← Nat.add_assoc, pow_succ, map_mul, hp, mul_zero]
local notation "L" => coefficientShearTerminalEquationIso
  data Q r (s + 1) hs hsNext (lin).1 (lin).2 g6 hr a ha
local notation "I" => coefficientShearRetainedEquationIso data Q r (s + 1) hs
  ⟨s, Nat.lt_succ_self s⟩ hscale hp (lin).1 (lin).2
local notation "ψ" => tensorShearTerminalNodeConicMap W π (0 + s)
  (d).b3 (d).b4 (d).b6 Q r hscale hp (lin).1 (lin).2 hr g6 a ha
local notation "b" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom ψ))
local notation "inc" => PrincipalOpenTransport.inclusion (conicT (U).a₁ c)
local notation "ρ" => ProjectiveLine.endpointReversal Q
local notation "D" => coefficientShearResidueStrictZeroAtlasCoconeMap
  hπ hm data s hs hk h3 h4 h6 hc C

local notation "A" => coefficientShearAtlasMap hπ data Q r (s + 1) hs
local notation "last" => Sum.inr (Fin.mk s (Nat.lt_succ_self s))
local notation "P" => coefficientShearTerminalNodeAtlasPullbackIso
  hπ data Q r s hs hscale hp (lin).1 (lin).2 g6 hr a ha

local notation "hu" => Eq.mp (congrArg IsUnit ha) (Units.isUnit a)

omit [IsBezout R] in
/-- The whole last conic receives the two independent terminal component maps. -/
theorem coefficientShearResidueStrictZeroAtlasCoconeMap_last_conic :
    middleConicImmersion U c h2 ≫ (I).hom ≫ D last =
      conicZeroProjectiveDesc (U).a₁ c hu g6
        (ρ ≫ F ⟨s + 1, by omega⟩) (F ⟨2 * s + 2 - s, by omega⟩) := by
  have hmap (i : Fin (s + 1)) (hi : 0 < i.val) :
      D (.inr i) = coefficientShearResidueStrictZeroRetainedDesc
        hπ hm data s hs hk h3 h4 h6 hc i hi F w := by
    obtain ⟨j, rfl⟩ := Fin.eq_succ_of_ne_zero (show i ≠ 0 from by
      intro h
      simp only [h, Fin.val_zero, lt_self_iff_false] at hi)
    exact coefficientShearResidueStrictZeroAtlasCoconeMap_positive
      hπ hm data s hs hk h3 h4 h6 hc C j
  rw [hmap ⟨s, Nat.lt_succ_self s⟩ hspos, coefficientShearResidueStrictZeroRetainedDesc,
    coefficientShearRetainedZeroDesc]
  erw [coefficientShearRetainedEquationDesc_conic
    data Q r (s + 1) hs ⟨s, Nat.lt_succ_self s⟩ hscale hp (lin).1 (lin).2 hr hu]

omit [IsBezout R] in
/-- The complete last conic and divided node agree on their full original boundary. -/
theorem coefficientShearResidueStrictZeroAtlasCoconeMap_terminal_boundary :
    inc ≫ middleConicImmersion U c h2 ≫ (I).hom ≫ D last =
      b ≫ (L).hom ≫ D (.inl 1) := by
  rw [coefficientShearResidueStrictZeroAtlasCoconeMap_last_conic (hspos := hspos)]
  refine coefficientShearTerminalNodeBoundary_desc
    W π (0 + s) (d).b3 (d).b4 (d).b6 Q r hscale hp (lin).1 (lin).2 hr g6 a ha
    (ρ ≫ F ⟨s + 1, by omega⟩) (F ⟨2 * s + 2 - s, by omega⟩)
    ((L).hom ≫ D (.inl 1)) ?_ ?_
  · rw [ProjectiveLine.right_endpointReversal_assoc, ← Category.assoc]
    change coefficientShearTerminalEquationSecond
      data Q r (s + 1) hs hsNext (lin).1 (lin).2 g6 hr a ha ≫ D (.inl 1) = _
    rw [coefficientShearResidueStrictZeroAtlasCoconeMap_divided,
      coefficientShearResidueStrictDividedDesc_second]
  · rw [← Category.assoc]
    change coefficientShearTerminalEquationFirst
      data Q r (s + 1) hs hsNext (lin).1 (lin).2 g6 hr a ha ≫ D (.inl 1) = _
    rw [coefficientShearResidueStrictZeroAtlasCoconeMap_divided,
      coefficientShearResidueStrictDividedDesc_first]
    congr 2
    apply Fin.ext
    change s + 1 + 1 = 2 * s + 2 - s
    omega

/-- The entire terminal node/retained pullback satisfies the strict cocone gluing equation. -/
theorem coefficientShearResidueStrictZeroAtlasCoconeMap_terminal_pullback :
    pullback.fst (A (.inl 1)) (A last) ≫ D (.inl 1) =
      pullback.snd (A (.inl 1)) (A last) ≫ D last := by
  apply (cancel_epi (P).hom).mp
  simp only [← Category.assoc, coefficientShearTerminalNodeAtlasPullbackIso_fst,
    coefficientShearTerminalNodeAtlasPullbackIso_snd]
  simpa only [Category.assoc] using
    (coefficientShearResidueStrictZeroAtlasCoconeMap_terminal_boundary
      hπ hm data s hs hk hspos h3 h4 h6 hc C).symm

end FLT.Mazur.WeierstrassDividedDepth
