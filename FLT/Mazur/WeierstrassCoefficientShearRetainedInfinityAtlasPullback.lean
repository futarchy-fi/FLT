/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearAtlasComparison
public import FLT.Mazur.WeierstrassDividedOlderResidueInfinity
import all FLT.Mazur.WeierstrassCoefficientShearAtlasComparison
import all FLT.Mazur.WeierstrassDividedOlderResidueInfinity

/-!
# Empty full retained intersections with the original infinity chart

At positive residue depth every full retained equation misses the original
infinity equation. Arbitrary maps therefore satisfy both ordered gluing equations.
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
  (t : ℕ) (ht : t ≤ n) (i : Fin t) (hi0 : 0 < start + i.val)
  (hp : algebraMap R S π = 0)
local notation "A" => coefficientShearAtlasMap hπ data S r t ht
include hi0 hp

/-- A whole positive-depth retained equation misses the original infinity equation. -/
theorem coefficientShearAtlas_retained_infinity_disjoint :
    Disjoint (Set.range (A (.inr i))) (Set.range (A (.inl 0))) := by
  rcases i with ⟨i, hi⟩
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hi
  rw [coefficientShearAtlasMap_range, coefficientShearAtlasMap_range]
  have H := olderIndexedResidue_infinity_disjoint S hπ data i (by omega) m ht hp hi0
  have hRet : coefficientShearAtlasIndex (i + 1 + m) (.inr ⟨i, hi⟩) =
      (Fin.mk (m + 1) (by omega)).succ := by
    apply Fin.ext
    change i + 1 + m - i + 1 = m + 1 + 1
    omega
  rw [hRet]
  exact H

/-- The full retained/infinity pullback is the empty scheme. -/
theorem coefficientShearAtlas_retained_infinity_isPullback :
    IsPullback (Scheme.emptyTo _) (Scheme.emptyTo _) (A (.inr i)) (A (.inl 0)) := by
  let _ := Scheme.isEmpty_pullback (A (.inr i)) (A (.inl 0))
    (coefficientShearAtlas_retained_infinity_disjoint hπ data S r t ht i hi0 hp)
  apply IsPullback.of_iso_pullback ⟨Scheme.empty_ext _ _⟩
    (asIso (Scheme.emptyTo (pullback (A (.inr i)) (A (.inl 0)))))
  · exact Scheme.empty_ext _ _
  · exact Scheme.empty_ext _ _

/-- Whole retained and infinity chart maps agree on the original full intersection. -/
theorem coefficientShearAtlas_retained_infinity_compatible {Y : Scheme.{u}}
    (f : coefficientShearAtlasObject data S r t ht (.inr i) ⟶ Y)
    (g : coefficientShearAtlasObject data S r t ht (.inl 0) ⟶ Y) :
    pullback.fst (A (.inr i)) (A (.inl 0)) ≫ f =
      pullback.snd (A (.inr i)) (A (.inl 0)) ≫ g := by
  let _ := Scheme.isEmpty_pullback (A (.inr i)) (A (.inl 0))
    (coefficientShearAtlas_retained_infinity_disjoint hπ data S r t ht i hi0 hp)
  exact isInitialOfIsEmpty.hom_ext _ _

/-- The reversed infinity/retained ordered pair is compatible as well. -/
theorem coefficientShearAtlas_infinity_retained_compatible {Y : Scheme.{u}}
    (f : coefficientShearAtlasObject data S r t ht (.inr i) ⟶ Y)
    (g : coefficientShearAtlasObject data S r t ht (.inl 0) ⟶ Y) :
    pullback.fst (A (.inl 0)) (A (.inr i)) ≫ g =
      pullback.snd (A (.inl 0)) (A (.inr i)) ≫ f := by
  let _ := Scheme.isEmpty_pullback (A (.inl 0)) (A (.inr i))
    (coefficientShearAtlas_retained_infinity_disjoint hπ data S r t ht i hi0 hp).symm
  exact isInitialOfIsEmpty.hom_ext _ _

end FLT.Mazur.WeierstrassDividedDepth
