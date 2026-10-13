/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearResidueZeroAtlasTerminalPullback
import all FLT.Mazur.WeierstrassCoefficientShearResidueZeroAtlasTerminalPullback
public import FLT.Mazur.WeierstrassCoefficientShearEqualityDividedExclusions
public import FLT.Mazur.WeierstrassCoefficientShearScaleOneDividedExclusions
public import FLT.Mazur.WeierstrassCoefficientShearResidueZeroLengthTwoPullback
import all FLT.Mazur.WeierstrassCoefficientShearResidueZeroAtlasCoconeMaps

/-!
# All full divided-chart pairings in the original start-zero residue atlas

The final retained neighbor uses its complete conic-Laurent overlap. Earlier
retained equations, the initial equation, and infinity have empty intersections.
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
  (s : ℕ) (hs : s + 1 ≤ n) (he : 2 * (0 + (s + 1)) = depth)
  (h3 : W.a₃ ∈ maximalIdeal R ^ (depth + 1))
  (h4 : W.a₄ ∈ maximalIdeal R ^ (depth + 1))
  (h6next : W.a₆ ∉ maximalIdeal R ^ (depth + 1)) (hc : IsUnit W.c₄)
local notation "V" => W.map (residue R)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial V)
local notation "r" => AdjoinRoot.root (nodeTangentPolynomial V)
variable [Fact (Irreducible (nodeTangentPolynomial (W.map (residue R))))]
open WeierstrassModificationX WeierstrassSuccessiveX WeierstrassDilatation
local notation "d" => data ⟨s + 1, Nat.lt_succ_of_le hs⟩
local notation "a" => residueTangentComponentUnit W h3 h4 hc
local notation "ha" => residueTangentComponentUnit_val W h3 h4 hc
variable (C : PushoutCocone (PolygonPinching.toComponents
    (AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))) (2 * s + 2)
    (Nat.zero_lt_succ (2 * s + 1)))
  (PolygonPinching.toNodes
    (AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))) (2 * s + 2)))
local notation "F" => PolygonCyclicPushout.inputComponent Q (2 * s + 2) C.inl
local notation "w" => fun i => by
  simpa only [PolygonCyclicAtlas.next_eq_rotate] using
    PolygonCyclicPushout.input_condition Q (2 * s + 2) (by omega) C.inl C.inr C.condition i

local notation "lin" => nodalDepth_tangent_linear_zero hπ hm d (Nat.le_of_eq he) h3 h4
local notation "cunit" => nodalDepth_tangent_constant_isUnit hm d he h6next
local notation "hp" => residueTangentEquation_zero W π
  (hm ▸ Ideal.mem_span_singleton_self π)
local notation "hr" => residueTangentEquation_root W
local notation "D" => coefficientShearResidueZeroAtlasCoconeMap
  hπ hm data s hs he h3 h4 h6next hc C

local notation "A" => coefficientShearAtlasMap hπ data Q r (s + 1) hs
local notation "last" => Sum.inr (Fin.mk s (Nat.lt_succ_self s))
/-- Every full divided/retained intersection satisfies the actual cocone equation. -/
theorem coefficientShearResidueZeroAtlasCoconeMap_divided_retained_pullback
    (i : Fin (s + 1)) :
    pullback.fst (A (.inl 1)) (A (.inr i)) ≫ D (.inl 1) =
      pullback.snd (A (.inl 1)) (A (.inr i)) ≫ D (.inr i) := by
  by_cases hs0 : s = 0
  · subst s
    have hi : i = ⟨0, by decide⟩ := Fin.ext (by omega)
    subst i
    exact coefficientShearResidueZeroAtlasCoconeMap_lengthTwo_pullback
      hπ hm data hs he h3 h4 h6next hc C
  have hspos : 0 < s := Nat.pos_of_ne_zero hs0
  have hscale := nodalDepth_tangent_scale_zero (W := W) hm
    (show 0 < 0 + s from by omega)
  by_cases hi : i.val = s
  · have hi' : i = ⟨s, Nat.lt_succ_self s⟩ := Fin.ext hi
    subst i
    exact coefficientShearResidueZeroAtlasCoconeMap_terminal_pullback
      hπ hm data s hs he hspos h3 h4 h6next hc C
  · let _ := Scheme.isEmpty_pullback (A (.inl 1)) (A (.inr i))
      (coefficientShearEqualityDivided_retained_disjoint
        hπ data Q r s hs hscale hp (lin).1 (lin).2 cunit hr a ha i (by omega))
    exact isInitialOfIsEmpty.hom_ext _ _

/-- Reversed divided/retained pairs keep compatibility on the full scheme pullback. -/
theorem coefficientShearResidueZeroAtlasCoconeMap_retained_divided_pullback
    (i : Fin (s + 1)) :
    pullback.fst (A (.inr i)) (A (.inl 1)) ≫ D (.inr i) =
      pullback.snd (A (.inr i)) (A (.inl 1)) ≫ D (.inl 1) := by
  apply (cancel_epi (pullbackSymmetry (A (.inl 1)) (A (.inr i))).hom).mp
  simpa only [pullbackSymmetry_hom_comp_fst_assoc, pullbackSymmetry_hom_comp_snd_assoc]
    using (coefficientShearResidueZeroAtlasCoconeMap_divided_retained_pullback
      hπ hm data s hs he h3 h4 h6next hc C i).symm

/-- The full divided and initial equations agree on their empty scheme intersection. -/
theorem coefficientShearResidueZeroAtlasCoconeMap_divided_initial_pullback :
    pullback.fst (A (.inl 1)) (A (.inl 2)) ≫ D (.inl 1) =
      pullback.snd (A (.inl 1)) (A (.inl 2)) ≫ D (.inl 2) := by
  have hlin := lin
  have hunit := cunit
  have hd : Disjoint (Set.range (A (.inl 1))) (Set.range (A (.inl 2))) := by
    by_cases hs0 : s = 0
    · subst s
      exact coefficientShearScaleOneEqualityDivided_initial_disjoint
        hπ data Q r 0 hs (by simp) hp hlin.1 hlin.2 hunit hr a ha
    · have hscale := nodalDepth_tangent_scale_zero (W := W) hm
        (show 0 < 0 + s from by omega)
      exact coefficientShearEqualityDivided_initial_disjoint
        hπ data Q r s hs hscale hp hlin.1 hlin.2 hunit hr a ha
  let _ := Scheme.isEmpty_pullback (A (.inl 1)) (A (.inl 2)) hd
  exact isInitialOfIsEmpty.hom_ext _ _

/-- The full divided and infinity equations agree on their empty scheme intersection. -/
theorem coefficientShearResidueZeroAtlasCoconeMap_divided_infinity_pullback :
    pullback.fst (A (.inl 1)) (A (.inl 0)) ≫ D (.inl 1) =
      pullback.snd (A (.inl 1)) (A (.inl 0)) ≫ D (.inl 0) := by
  have hlin := lin
  have hunit := cunit
  have hd : Disjoint (Set.range (A (.inl 1))) (Set.range (A (.inl 0))) := by
    by_cases hs0 : s = 0
    · subst s
      exact coefficientShearScaleOneEqualityDivided_infinity_disjoint
        hπ data Q r 0 hs (by simp) hp hlin.1 hlin.2 hunit hr a ha
    · have hscale := nodalDepth_tangent_scale_zero (W := W) hm
        (show 0 < 0 + s from by omega)
      exact coefficientShearEqualityDivided_infinity_disjoint
        hπ data Q r s hs hscale hp hlin.1 hlin.2 hunit hr a ha (by omega)
  let _ := Scheme.isEmpty_pullback (A (.inl 1)) (A (.inl 0)) hd
  exact isInitialOfIsEmpty.hom_ext _ _

end FLT.Mazur.WeierstrassDividedDepth
