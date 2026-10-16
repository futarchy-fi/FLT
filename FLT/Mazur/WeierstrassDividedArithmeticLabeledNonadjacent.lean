/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticLabeledEarlierTerminal
public import FLT.Mazur.WeierstrassDividedArithmeticNonadjacentIntersection

/-!
# Nonadjacent exclusions in the full labeled arithmetic atlas

The indexed empty intersections exclude every nonconsecutive retained pair,
regardless of label, and every initial label against a positive retained depth.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticLabeledAtlasMap
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (m : ℕ)

/-- The indexed nonadjacent exclusions retain the fixed arithmetic atlas morphisms. -/
theorem arithmeticTensorAtlas_nonadjacent_disjoint (j r : ℕ) (hr : j + 2 + r ≤ n)
    (i : Fin (j + 1)) :
    Disjoint
      (Set.range (arithmeticTensorAtlasMap hπ data m (j + 2 + r) hr
        (Fin.succ ⟨i.val + 2 + r + 1, by omega⟩)))
      (Set.range (arithmeticTensorAtlasMap hπ data m (j + 2 + r) hr
        (Fin.succ ⟨r + 1, by omega⟩))) :=
  nonadjacentArithmeticTensorAtlas_disjoint hπ data m j (by omega) (by omega) r hr i

attribute [local irreducible] arithmeticTensorAtlasMap
variable (H : ArithmeticAtlasCoefficients data) (k : ℕ) (hk : k ≤ n)
local notation "c" => arithmeticLabeledAtlasMap hπ data H m k hk

/-- Nonconsecutive retained depths have disjoint full labeled images. -/
theorem arithmeticLabeledAtlas_nonadjacent_disjoint (a b : Fin k)
    (hab : a.val + 1 < b.val) (u v : Bool) :
    Disjoint (Set.range (c (.retained a u))) (Set.range (c (.retained b v))) := by
  apply Disjoint.mono
    (arithmeticLabeledAtlas_retained_range_subset hπ data H m k hk a u)
    (arithmeticLabeledAtlas_retained_range_subset hπ data H m k hk b v)
  rcases a with ⟨a, ha⟩
  rcases b with ⟨b, hb⟩
  cases b with
  | zero => change a + 1 < 0 at hab; omega
  | succ j =>
    obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le (show j + 2 ≤ k by omega)
    change a + 1 < j + 1 at hab
    have hi : j - a - 1 < j + 1 := by omega
    have P := arithmeticTensorAtlas_nonadjacent_disjoint hπ data m j r hk ⟨j - a - 1, hi⟩
    have hleft : j - a - 1 + 2 + r + 1 = j + 2 + r - a := by
      omega
    have hright : r + 1 = j + 2 + r - (j + 1) := by omega
    have hl := congrArg
      (fun i : Fin (j + 2 + r + 3) =>
        Set.range (arithmeticTensorAtlasMap hπ data m (j + 2 + r) hk i))
      (congrArg Fin.succ (show
        (⟨j - a - 1 + 2 + r + 1, by omega⟩ : Fin (j + 2 + r + 2)) =
          ⟨j + 2 + r - a, by omega⟩ from Fin.ext hleft))
    have hr := congrArg
      (fun i : Fin (j + 2 + r + 3) =>
        Set.range (arithmeticTensorAtlasMap hπ data m (j + 2 + r) hk i))
      (congrArg Fin.succ (show
        (⟨r + 1, by omega⟩ : Fin (j + 2 + r + 2)) =
          ⟨j + 2 + r - (j + 1), by omega⟩ from Fin.ext hright))
    rw [hl, hr] at P
    exact P

/-- Every full nonconsecutive labeled intersection is the empty scheme. -/
theorem arithmeticLabeledAtlas_nonadjacent_isPullback (a b : Fin k)
    (hab : a.val + 1 < b.val) (u v : Bool) :
    IsPullback (Scheme.emptyTo _) (Scheme.emptyTo _)
      (c (.retained a u)) (c (.retained b v)) := by
  let _ := Scheme.isEmpty_pullback (c (.retained a u)) (c (.retained b v))
    (arithmeticLabeledAtlas_nonadjacent_disjoint hπ data m H k hk a b hab u v)
  apply IsPullback.of_iso_pullback ⟨Scheme.empty_ext _ _⟩
    (asIso (Scheme.emptyTo (pullback (c (.retained a u)) (c (.retained b v)))))
  · exact Scheme.empty_ext _ _
  · exact Scheme.empty_ext _ _

/-- Initial labels meet no retained depth beyond the first, for either retained label. -/
theorem arithmeticLabeledAtlas_initial_nonadjacent_disjoint (a : Fin k)
    (ha : 0 < a.val) (u v : Bool) :
    Disjoint (Set.range (c (.initial u))) (Set.range (c (.retained a v))) := by
  apply Disjoint.mono
    (arithmeticLabeledAtlas_initial_range_subset hπ data H m k hk u)
    (arithmeticLabeledAtlas_retained_range_subset hπ data H m k hk a v)
  rcases a with ⟨a, hak⟩
  cases a with
  | zero => change 0 < 0 at ha; omega
  | succ j =>
    obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le (show j + 2 ≤ k by omega)
    have P := arithmeticTensorAtlas_nonadjacent_disjoint hπ data m j r hk ⟨j, by omega⟩
    have hright : r + 1 = j + 2 + r - (j + 1) := by omega
    have hr := congrArg
      (fun i : Fin (j + 2 + r + 3) =>
        Set.range (arithmeticTensorAtlasMap hπ data m (j + 2 + r) hk i))
      (congrArg Fin.succ (show
        (⟨r + 1, by omega⟩ : Fin (j + 2 + r + 2)) =
          ⟨j + 2 + r - (j + 1), by omega⟩ from Fin.ext hright))
    rw [hr] at P
    exact P

/-- Initial versus positive-depth labeled fiber products are empty at every arithmetic order. -/
theorem arithmeticLabeledAtlas_initial_nonadjacent_isPullback (a : Fin k)
    (ha : 0 < a.val) (u v : Bool) :
    IsPullback (Scheme.emptyTo _) (Scheme.emptyTo _) (c (.initial u)) (c (.retained a v)) := by
  let _ := Scheme.isEmpty_pullback (c (.initial u)) (c (.retained a v))
    (arithmeticLabeledAtlas_initial_nonadjacent_disjoint hπ data m H k hk a ha u v)
  apply IsPullback.of_iso_pullback ⟨Scheme.empty_ext _ _⟩
    (asIso (Scheme.emptyTo (pullback (c (.initial u)) (c (.retained a v)))))
  · exact Scheme.empty_ext _ _
  · exact Scheme.empty_ext _ _

end FLT.Mazur.WeierstrassDividedDepth
