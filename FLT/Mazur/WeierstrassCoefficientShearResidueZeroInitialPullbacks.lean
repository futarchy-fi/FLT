/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearResidueZeroFirstExterior
public import FLT.Mazur.WeierstrassCoefficientShearResidueZeroInitialBoundary
public import FLT.Mazur.WeierstrassCoefficientShearInitialLaterAtlasPullback
public import FLT.Mazur.WeierstrassCoefficientShearResidueAtlasAdjacentPullback
import all FLT.Mazur.WeierstrassCoefficientShearResidueZeroAtlasCoconeMaps
import all FLT.Mazur.WeierstrassCoefficientShearResidueZeroFirstExterior
import all FLT.Mazur.WeierstrassCoefficientShearResidueZeroInitialBoundary

/-!
# All full initial and retained start-zero cocone intersections

The first chart uses its entire original slope boundary at either conic constant.
Every later retained intersection is empty by the actual atlas geometry.
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
  (s : ℕ) (hs : s + 1 ≤ n)
  (he : 2 * (0 + (s + 1)) = depth)
  (h3 : W.a₃ ∈ maximalIdeal R ^ (depth + 1))
  (h4 : W.a₄ ∈ maximalIdeal R ^ (depth + 1))
  (h6next : W.a₆ ∉ maximalIdeal R ^ (depth + 1)) (hc : IsUnit W.c₄)
local notation "V" => W.map (residue R)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial V)
local notation "r" => AdjoinRoot.root (nodeTangentPolynomial V)
variable [Fact (Irreducible (nodeTangentPolynomial (W.map (residue R))))]
variable (C : PushoutCocone (PolygonPinching.toComponents
    (AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))) (2 * s + 2)
    (Nat.zero_lt_succ (2 * s + 1)))
  (PolygonPinching.toNodes
    (AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))) (2 * s + 2)))
local notation "F" => PolygonCyclicPushout.inputComponent Q (2 * s + 2) C.inl
local notation "w" => fun i => by
  simpa only [PolygonCyclicAtlas.next_eq_rotate] using
    PolygonCyclicPushout.input_condition Q (2 * s + 2) (by omega) C.inl C.inr C.condition i

open WeierstrassModificationX WeierstrassSuccessiveX
local notation "e" => data ⟨1, by omega⟩
local notation "lin" => nodalDepth_tangent_linear_zero hπ hm e (by dsimp; omega) h3 h4
local notation "hp" => residueTangentEquation_zero W π
  (hm ▸ Ideal.mem_span_singleton_self π)
local notation "hr" => residueTangentEquation_root W
local notation "hscale" => show algebraMap R Q (π ^ (0 + 0)) = 1 from by simp
local notation "a" => residueTangentComponentUnit W h3 h4 hc
local notation "E" => coefficientShearRetainedScaleOneTensorIso
  data Q r (s + 1) hs ⟨0, Nat.zero_lt_succ s⟩
local notation "L" => Spec.map (CommRingCat.ofHom (tensorShearScaleOneIncidenceMap
  W (π ^ (0 + 0)) π (e).b3 (e).b4 (e).b6 Q r hscale hp (lin).1 (lin).2 hr).toRingHom)
local notation "D" => coefficientShearResidueZeroAtlasCoconeMap
  hπ hm data s hs he h3 h4 h6next hc C

local notation "atlas" => coefficientShearAtlasMap hπ data Q r (s + 1) hs

/-- The complete initial/first-retained pullback satisfies the original cocone equation. -/
theorem coefficientShearResidueZeroAtlasCoconeMap_initial_first_pullback :
    pullback.fst (atlas (.inl 2)) (atlas (.inr ⟨0, Nat.zero_lt_succ s⟩)) ≫ D (.inl 2) =
      pullback.snd (atlas (.inl 2)) (atlas (.inr ⟨0, Nat.zero_lt_succ s⟩)) ≫
        D (.inr ⟨0, Nat.zero_lt_succ s⟩) := by
  apply fullAtlasPullback_compatible
    (coefficientShearResidueZeroInitialBoundary_isPullback
      hπ hm data s hs (lin).1 (lin).2)
  rw [coefficientShearResidueZeroAtlasCoconeMap_initial]
  rw [coefficientShearResidueZeroInitialCoconeDesc_slope]
  simp only [Category.assoc]
  congr 1
  exact (coefficientShearResidueZeroAtlasCoconeMap_first_exterior
    hπ hm data s hs he h3 h4 h6next hc C).symm

/-- Every full initial/retained intersection satisfies the same cocone equation. -/
theorem coefficientShearResidueZeroAtlasCoconeMap_initial_retained_pullback
    (i : Fin (s + 1)) :
    pullback.fst (atlas (.inl 2)) (atlas (.inr i)) ≫ D (.inl 2) =
      pullback.snd (atlas (.inl 2)) (atlas (.inr i)) ≫ D (.inr i) := by
  by_cases hi : i = 0
  · subst i
    exact coefficientShearResidueZeroAtlasCoconeMap_initial_first_pullback
      hπ hm data s hs he h3 h4 h6next hc C
  · exact coefficientShearAtlas_initial_later_compatible
      hπ data Q r (s + 1) hs i (by simpa using Fin.pos_iff_ne_zero.mpr hi) hp _ _

/-- Both orders of every initial/retained overlap satisfy the complete cocone equation. -/
theorem coefficientShearResidueZeroAtlasCoconeMap_retained_initial_pullback
    (i : Fin (s + 1)) :
    pullback.fst (atlas (.inr i)) (atlas (.inl 2)) ≫ D (.inr i) =
      pullback.snd (atlas (.inr i)) (atlas (.inl 2)) ≫ D (.inl 2) := by
  apply (cancel_epi (pullbackSymmetry (atlas (.inl 2)) (atlas (.inr i))).hom).mp
  simpa only [pullbackSymmetry_hom_comp_fst_assoc, pullbackSymmetry_hom_comp_snd_assoc]
    using (coefficientShearResidueZeroAtlasCoconeMap_initial_retained_pullback
      hπ hm data s hs he h3 h4 h6next hc C i).symm

end FLT.Mazur.WeierstrassDividedDepth
