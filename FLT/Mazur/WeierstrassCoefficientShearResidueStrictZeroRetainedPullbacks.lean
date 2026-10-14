/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearResidueStrictZeroPositiveAdjacentPullback
public import FLT.Mazur.WeierstrassCoefficientShearResidueStrictZeroFirstAdjacentPullback
public import FLT.Mazur.WeierstrassCoefficientShearNonadjacentAtlasPullback
import all FLT.Mazur.WeierstrassCoefficientShearResidueStrictZeroPositiveAdjacentPullback
import all FLT.Mazur.WeierstrassCoefficientShearResidueStrictZeroFirstAdjacentPullback
import all FLT.Mazur.WeierstrassCoefficientShearResidueStrictZeroAtlasMaps

/-!
# All full retained pair compatibilities of the original start-zero cocone

Equal, adjacent, and nonadjacent retained charts satisfy the full gluing
condition, in arbitrary order.
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
  (h3 : W.a₃ ∈ maximalIdeal R ^ (depth + 1))
  (h4 : W.a₄ ∈ maximalIdeal R ^ (depth + 1))
  (h6 : W.a₆ ∈ maximalIdeal R ^ depth) (hc : IsUnit W.c₄)
local notation "V" => W.map (residue R)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial V)
local notation "r" => AdjoinRoot.root (nodeTangentPolynomial V)
variable [Fact (Irreducible (nodeTangentPolynomial (W.map (residue R))))]
open WeierstrassModificationX WeierstrassSuccessiveX WeierstrassDilatation
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

local notation "A" => coefficientShearAtlasMap hπ data Q r (s + 1) hs
local notation "D" => coefficientShearResidueStrictZeroAtlasCoconeMap
  hπ hm data s hs hk h3 h4 h6 hc C
local notation "hp" => residueTangentEquation_zero W π
  (hm ▸ Ideal.mem_span_singleton_self π)

/-- Increasing retained indices satisfy the actual whole-pullback gluing equation. -/
theorem coefficientShearResidueStrictZeroAtlasCoconeMap_retained_ordered
    (i k : Fin (s + 1)) (hik : i.val < k.val) :
    pullback.fst (A (.inr i)) (A (.inr k)) ≫ D (.inr i) =
      pullback.snd (A (.inr i)) (A (.inr k)) ≫ D (.inr k) := by
  by_cases hj : i.val + 1 = k.val
  · have hi : i.val < s := by omega
    have hK : k = ⟨i.val + 1, Nat.succ_lt_succ hi⟩ := Fin.ext hj.symm
    subst k
    by_cases hi0 : i.val = 0
    · have hI : i = ⟨0, Nat.zero_lt_succ s⟩ := Fin.ext hi0
      subst i
      exact coefficientShearResidueStrictZeroAtlasCoconeMap_first_adjacent_pullback
        hπ hm data s hs hk h3 h4 h6 hc C (by simpa using hi)
    · exact coefficientShearResidueStrictZeroAtlasCoconeMap_adjacent_pullback
        hπ hm data s hs hk h3 h4 h6 hc C ⟨i.val, hi⟩ (Nat.pos_of_ne_zero hi0)
  · exact coefficientShearAtlas_nonadjacent_compatible hπ data Q r (s + 1) hs
      i k (by omega) hp (D (.inr i)) (D (.inr k))

/-- Every pair of full retained equations has compatible actual cocone maps. -/
theorem coefficientShearResidueStrictZeroAtlasCoconeMap_retained_pullback
    (i k : Fin (s + 1)) :
    pullback.fst (A (.inr i)) (A (.inr k)) ≫ D (.inr i) =
      pullback.snd (A (.inr i)) (A (.inr k)) ≫ D (.inr k) := by
  rcases lt_trichotomy i.val k.val with hik | hik | hik
  · exact coefficientShearResidueStrictZeroAtlasCoconeMap_retained_ordered
      hπ hm data s hs hk h3 h4 h6 hc C i k hik
  · have h : i = k := Fin.ext hik
    subst k
    have hproj : pullback.fst (A (.inr i)) (A (.inr i)) =
        pullback.snd (A (.inr i)) (A (.inr i)) :=
      (cancel_mono (A (.inr i))).mp pullback.condition
    rw [hproj]
  · apply (cancel_epi (pullbackSymmetry (A (.inr k)) (A (.inr i))).hom).mp
    simpa only [pullbackSymmetry_hom_comp_fst_assoc, pullbackSymmetry_hom_comp_snd_assoc]
      using (coefficientShearResidueStrictZeroAtlasCoconeMap_retained_ordered
        hπ hm data s hs hk h3 h4 h6 hc C k i hik).symm

end FLT.Mazur.WeierstrassDividedDepth
