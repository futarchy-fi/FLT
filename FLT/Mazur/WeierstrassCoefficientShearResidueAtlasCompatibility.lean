/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearResidueAtlasInfinityPullback
import all FLT.Mazur.WeierstrassCoefficientShearResidueAtlasInfinityPullback
import all FLT.Mazur.WeierstrassCoefficientShearResidueAtlasInitialPullbacks
import all FLT.Mazur.WeierstrassCoefficientShearResidueAtlasRetainedPullbacks
public import FLT.Mazur.WeierstrassCoefficientShearResidueAtlasRetainedPullbacks
public import FLT.Mazur.WeierstrassCoefficientShearResidueAtlasDividedPullbacks
public import FLT.Mazur.WeierstrassCoefficientShearRetainedInfinityAtlasPullback
import all FLT.Mazur.WeierstrassCoefficientShearResidueAtlasDividedPullbacks
import all FLT.Mazur.WeierstrassCoefficientShearResidueAtlasCoconeMaps

/-!
# All actual original residue atlas pairs satisfy the cocone equation

This includes all distinguished pairs, equal indices, both orders, and every
retained component at every positive initial depth, including the first-last case.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0)
  (hm : maximalIdeal R = Ideal.span {π}) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (s : ℕ) (hs : s + 1 ≤ n) (he : 2 * (start + (s + 1)) = depth)
  (hstart : 0 < start)
  (h3 : W.a₃ ∈ maximalIdeal R ^ (depth + 1))
  (h4 : W.a₄ ∈ maximalIdeal R ^ (depth + 1))
  (h6 : W.a₆ ∈ maximalIdeal R ^ depth)
  (h6next : W.a₆ ∉ maximalIdeal R ^ (depth + 1)) (hc : IsUnit W.c₄)
local notation "V" => W.map (residue R)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial V)
local notation "r" => AdjoinRoot.root (nodeTangentPolynomial V)
variable [Fact (Irreducible (nodeTangentPolynomial (W.map (residue R))))]
open WeierstrassModificationX WeierstrassSuccessiveX WeierstrassDilatation
local notation "a" => residueTangentComponentUnit W h3 h4 hc
local notation "ha" => residueTangentComponentUnit_val W h3 h4 hc
variable (C : PushoutCocone (PolygonPinching.toComponents
    (AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))) (2 * s + 4) (by omega))
  (PolygonPinching.toNodes
    (AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))) (2 * s + 4)))
local notation "F" => PolygonCyclicPushout.inputComponent Q (2 * s + 4) C.inl
local notation "w" => fun i => by
  simpa only [PolygonCyclicAtlas.next_eq_rotate] using
    PolygonCyclicPushout.input_condition Q (2 * s + 4) (by omega) C.inl C.inr C.condition i

local notation "A" => coefficientShearAtlasMap hπ data Q r (s + 1) hs
local notation "D" => coefficientShearResidueAtlasCoconeMap
  hπ hm data s hs he hstart h3 h4 h6 h6next hc C
local notation "hp" => residueTangentEquation_zero W π
  (hm ▸ Ideal.mem_span_singleton_self π)

/-- Every two full actual atlas maps of the original pinching cocone are compatible. -/
theorem coefficientShearResidueAtlasCoconeMap_compatible
    (i j : Fin 3 ⊕ Fin (s + 1)) :
    pullback.fst (A i) (A j) ≫ D i = pullback.snd (A i) (A j) ≫ D j := by
  have rev (i j : Fin 3 ⊕ Fin (s + 1))
      (h : pullback.fst (A j) (A i) ≫ D j = pullback.snd (A j) (A i) ≫ D i) :
      pullback.fst (A i) (A j) ≫ D i = pullback.snd (A i) (A j) ≫ D j := by
    apply (cancel_epi (pullbackSymmetry (A j) (A i)).hom).mp
    simpa only [pullbackSymmetry_hom_comp_fst_assoc, pullbackSymmetry_hom_comp_snd_assoc]
      using h.symm
  by_cases hij : i = j
  · subst j
    have hproj : pullback.fst (A i) (A i) = pullback.snd (A i) (A i) :=
      (cancel_mono (A i)).mp pullback.condition
    rw [hproj]
  rcases i with i | i <;> rcases j with j | j
  · fin_cases i <;> fin_cases j
    · exact False.elim (hij rfl)
    · exact rev _ _ (coefficientShearResidueAtlasCoconeMap_divided_infinity_pullback
        hπ hm data s hs he hstart h3 h4 h6 h6next hc C)
    · exact coefficientShearResidueAtlasCoconeMap_infinity_initial_pullback
        hπ hm data s hs he hstart h3 h4 h6 h6next hc C
    · exact coefficientShearResidueAtlasCoconeMap_divided_infinity_pullback
        hπ hm data s hs he hstart h3 h4 h6 h6next hc C
    · exact False.elim (hij rfl)
    · exact coefficientShearResidueAtlasCoconeMap_divided_initial_pullback
        hπ hm data s hs he hstart h3 h4 h6 h6next hc C
    · exact coefficientShearResidueAtlasCoconeMap_initial_infinity_pullback
        hπ hm data s hs he hstart h3 h4 h6 h6next hc C
    · exact rev _ _ (coefficientShearResidueAtlasCoconeMap_divided_initial_pullback
        hπ hm data s hs he hstart h3 h4 h6 h6next hc C)
    · exact False.elim (hij rfl)
  · fin_cases i
    · exact coefficientShearAtlas_infinity_retained_compatible
        hπ data Q r (s + 1) hs j (by omega) hp _ _
    · exact coefficientShearResidueAtlasCoconeMap_divided_retained_pullback
        hπ hm data s hs he hstart h3 h4 h6 h6next hc C j
    · exact coefficientShearResidueAtlasCoconeMap_initial_retained_pullback
        hπ hm data s hs he hstart h3 h4 h6 h6next hc C j
  · fin_cases j
    · exact coefficientShearAtlas_retained_infinity_compatible
        hπ data Q r (s + 1) hs i (by omega) hp _ _
    · exact coefficientShearResidueAtlasCoconeMap_retained_divided_pullback
        hπ hm data s hs he hstart h3 h4 h6 h6next hc C i
    · exact coefficientShearResidueAtlasCoconeMap_retained_initial_pullback
        hπ hm data s hs he hstart h3 h4 h6 h6next hc C i
  · exact coefficientShearResidueAtlasCoconeMap_retained_pullback
      hπ hm data s hs he hstart h3 h4 h6 h6next hc C i j

end FLT.Mazur.WeierstrassDividedDepth
