/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeDoubleRankTestDetection

/-!
# One finite rank rectangle detects full coefficients at all orders

The geometric rank bound works simultaneously for every locally Noetherian
coefficient test. Both independent infinitesimal orders remain unbounded.
Neither compactness nor finiteness over the original scalar ring is required
of the test, and all equal-rank charts are included.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S B : Scheme.{0}} [IsNoetherian S]
  (E : Over S) [Etale E.hom] [IsSeparated E.hom] [QuasiCompact E.hom]
  (x y : B ⟶ S)

/-- A single complete finite rank rectangle detects exact sections on every full test. -/
theorem exists_bounded_doubleRank_test_detection :
    ∃ N : ℕ, ∀ (T : Scheme.{0}) (_ : IsLocallyNoetherian T)
      (v : T ⟶ B) (a b : Γ(B, ⊤)),
      (∀ n m : Fin (N + 1), ∀ r s : ℕ,
        (doubleRankMap E x y n.val m.val r s).appTop a =
          (doubleRankMap E x y n.val m.val r s).appTop b) →
      v.appTop a = v.appTop b := by
  obtain ⟨N, hN⟩ := exists_uniform_rank_bound E
  refine ⟨N, fun T hT v a b h ↦ ?_⟩
  let _ := hT
  have hcover (w : T ⟶ S) (z : T) : ∃ n ∈ Set.Iic N, w z ∈ exactRank E n := by
    obtain ⟨n, hn⟩ := exists_exactRank E (w z)
    exact ⟨n, hN _ n hn.1, hn⟩
  apply section_eq_of_doubleRank_stages E (v ≫ x) (v ≫ y)
    (Set.Iic N) (Set.Iic N) (hcover _) (hcover _)
  intro n hn m hm r s
  exact doubleRankTestMap_eq E x y v n m r s a b
    (h ⟨n, Nat.lt_succ_of_le hn⟩ ⟨m, Nat.lt_succ_of_le hm⟩ r s)

end FLT.Mazur.RelativeOrderedTuples
