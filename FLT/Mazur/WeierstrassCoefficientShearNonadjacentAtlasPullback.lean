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
# Empty full nonadjacent retained atlas intersections

The original indexed tensor disjointness transports to the actual sheared atlas.
Consequently arbitrary chart maps agree on every such full pullback.
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
  (t : ℕ) (ht : t ≤ n) (i k : Fin t) (hik : i.val + 1 < k.val)
  (hp : algebraMap R S π = 0)
local notation "A" => coefficientShearAtlasMap hπ data S r t ht
include hik hp

/-- Nonadjacent retained equations have disjoint images in the whole original model. -/
theorem coefficientShearAtlas_nonadjacent_disjoint :
    Disjoint (Set.range (A (.inr i))) (Set.range (A (.inr k))) := by
  rcases i with ⟨i, hi⟩
  rcases k with ⟨k, hk⟩
  change i + 1 < k at hik
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [coefficientShearAtlasMap_range, coefficientShearAtlasMap_range]
  have H := nonadjacentGlobalTensorAtlas_disjoint hπ data S j
    (by omega) (by omega) m ht ⟨j - 1 - i, by omega⟩ hp
  have hOld : coefficientShearAtlasIndex (j + 2 + m) (.inr ⟨i, hi⟩) =
      (Fin.mk (j - 1 - i + 2 + m + 1) (by omega)).succ := by
    apply Fin.ext
    change j + 2 + m - i + 1 = j - 1 - i + 2 + m + 1 + 1
    omega
  have hNew : coefficientShearAtlasIndex (j + 2 + m) (.inr ⟨j + 1, hk⟩) =
      (Fin.mk (m + 1) (by omega)).succ := by
    apply Fin.ext
    change j + 2 + m - (j + 1) + 1 = m + 1 + 1
    omega
  rw [hOld, hNew]
  exact H

/-- The entire nonadjacent scheme-theoretic intersection is the empty scheme. -/
theorem coefficientShearAtlas_nonadjacent_isPullback :
    IsPullback (Scheme.emptyTo _) (Scheme.emptyTo _) (A (.inr i)) (A (.inr k)) := by
  let _ := Scheme.isEmpty_pullback (A (.inr i)) (A (.inr k))
    (coefficientShearAtlas_nonadjacent_disjoint hπ data S r t ht i k hik hp)
  apply IsPullback.of_iso_pullback ⟨Scheme.empty_ext _ _⟩
    (asIso (Scheme.emptyTo (pullback (A (.inr i)) (A (.inr k)))))
  · exact Scheme.empty_ext _ _
  · exact Scheme.empty_ext _ _

/-- Arbitrary maps on nonadjacent retained charts agree on their full pullback. -/
theorem coefficientShearAtlas_nonadjacent_compatible {Y : Scheme.{u}}
    (f : coefficientShearAtlasObject data S r t ht (.inr i) ⟶ Y)
    (g : coefficientShearAtlasObject data S r t ht (.inr k) ⟶ Y) :
    pullback.fst (A (.inr i)) (A (.inr k)) ≫ f =
      pullback.snd (A (.inr i)) (A (.inr k)) ≫ g := by
  let _ := Scheme.isEmpty_pullback (A (.inr i)) (A (.inr k))
    (coefficientShearAtlas_nonadjacent_disjoint hπ data S r t ht i k hik hp)
  exact isInitialOfIsEmpty.hom_ext _ _

end FLT.Mazur.WeierstrassDividedDepth
