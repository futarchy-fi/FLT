/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearAtlasComparison
public import FLT.Mazur.WeierstrassDividedNonadjacentGlobalIntersection
import all FLT.Mazur.WeierstrassDividedNonadjacentGlobalIntersection
import all FLT.Mazur.WeierstrassCoefficientShearAtlasComparison

/-!
# Full initial atlas intersections with later retained equations

Except for the first retained equation, all original retained atlas objects
are disjoint from the full initial chart after the uniformizer vanishes.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [Field S] [Algebra R S] (r : S)
  (t : ℕ) (ht : t ≤ n) (k : Fin t) (hk0 : 0 < k.val)
  (hp : algebraMap R S π = 0)
local notation "A" => coefficientShearAtlasMap hπ data S r t ht
include hk0 hp

/-- The whole initial equation misses every retained equation except the first. -/
theorem coefficientShearAtlas_initial_later_disjoint :
    Disjoint (Set.range (A (.inl 2))) (Set.range (A (.inr k))) := by
  rcases k with ⟨k, hk⟩
  change 0 < k at hk0
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [coefficientShearAtlasMap_range, coefficientShearAtlasMap_range]
  have H := nonadjacentGlobalTensorAtlas_disjoint hπ data S j
    (by omega) (by omega) m ht ⟨j, by omega⟩ hp
  have hOld : coefficientShearAtlasIndex (j + 2 + m) (.inl 2) =
      (Fin.mk (j + 2 + m + 1) (by omega)).succ := by
    apply Fin.ext
    change j + 2 + m + 2 = j + 2 + m + 1 + 1
    omega
  have hNew : coefficientShearAtlasIndex (j + 2 + m) (.inr ⟨j + 1, hk⟩) =
      (Fin.mk (m + 1) (by omega)).succ := by
    apply Fin.ext
    change j + 2 + m - (j + 1) + 1 = m + 1 + 1
    omega
  rw [hOld, hNew]
  exact H

/-- These initial/later intersections are empty as full scheme pullbacks. -/
theorem coefficientShearAtlas_initial_later_isPullback :
    IsPullback (Scheme.emptyTo _) (Scheme.emptyTo _) (A (.inl 2)) (A (.inr k)) := by
  let _ := Scheme.isEmpty_pullback (A (.inl 2)) (A (.inr k))
    (coefficientShearAtlas_initial_later_disjoint hπ data S r t ht k hk0 hp)
  apply IsPullback.of_iso_pullback ⟨Scheme.empty_ext _ _⟩
    (asIso (Scheme.emptyTo (pullback (A (.inl 2)) (A (.inr k)))))
  · exact Scheme.empty_ext _ _
  · exact Scheme.empty_ext _ _

/-- Any full initial and later retained chart maps agree on their actual empty overlap. -/
theorem coefficientShearAtlas_initial_later_compatible {Y : Scheme.{u}}
    (f : coefficientShearAtlasObject data S r t ht (.inl 2) ⟶ Y)
    (g : coefficientShearAtlasObject data S r t ht (.inr k) ⟶ Y) :
    pullback.fst (A (.inl 2)) (A (.inr k)) ≫ f =
      pullback.snd (A (.inl 2)) (A (.inr k)) ≫ g := by
  let _ := Scheme.isEmpty_pullback (A (.inl 2)) (A (.inr k))
    (coefficientShearAtlas_initial_later_disjoint hπ data S r t ht k hk0 hp)
  exact isInitialOfIsEmpty.hom_ext _ _

/-- Compatibility also holds with the later retained chart ordered first. -/
theorem coefficientShearAtlas_later_initial_compatible {Y : Scheme.{u}}
    (f : coefficientShearAtlasObject data S r t ht (.inl 2) ⟶ Y)
    (g : coefficientShearAtlasObject data S r t ht (.inr k) ⟶ Y) :
    pullback.fst (A (.inr k)) (A (.inl 2)) ≫ g =
      pullback.snd (A (.inr k)) (A (.inl 2)) ≫ f := by
  let _ := Scheme.isEmpty_pullback (A (.inr k)) (A (.inl 2))
    (coefficientShearAtlas_initial_later_disjoint hπ data S r t ht k hk0 hp).symm
  exact isInitialOfIsEmpty.hom_ext _ _

end FLT.Mazur.WeierstrassDividedDepth
