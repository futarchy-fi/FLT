/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticPositiveEdgeCompatibility
public import FLT.Mazur.WeierstrassDividedArithmeticLabeledNonadjacent
public import FLT.Mazur.WeierstrassDividedArithmeticLabeledSeparation
public import FLT.Mazur.TernaryOpenDescent

/-!
# Full compatibility of every ordered pair of retained labels

The consecutive same-label equations suffice. Wrong labels at equal or
adjacent depth and all nonconsecutive depths have empty full intersections.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- An explicitly empty scheme fiber product imposes no compatibility condition. -/
theorem arithmeticEmptyPullback_compatible {U V X Y : Scheme.{0}}
    {i : U ⟶ X} {j : V ⟶ X}
    (T : IsPullback (Scheme.emptyTo U) (Scheme.emptyTo V) i j)
    (f : U ⟶ Y) (g : V ⟶ Y) :
    pullback.fst i j ≫ f = pullback.snd i j ≫ g := by
  apply (cancel_epi T.isoPullback.hom).mp
  simp only [← Category.assoc, IsPullback.isoPullback_hom_fst,
    IsPullback.isoPullback_hom_snd]
  exact Scheme.empty_ext _ _

attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
local notation "c" => arithmeticLabeledAtlasMap hπ data H m (j + 1) hj
variable {Y : Scheme.{0}}
  (f : ∀ i, arithmeticLabeledAtlasObject hπ data H m (j + 1) hj i ⟶ Y)
local notation "C" => fun (i k : ArithmeticChartLabel (j + 1)) =>
  pullback.fst (c i) (c k) ≫ f i = pullback.snd (c i) (c k) ≫ f k

/-- Consecutive original polygon equations imply all retained/retained fiber-product equations. -/
theorem arithmeticPositive_retained_compatible
    (hA : arithmeticPositiveAdjacentCompatible hπ data H m j hj f)
    (a b : Fin (j + 1)) (u v : Bool) : C (.retained a u) (.retained b v) := by
  have hE := (arithmeticPositiveAdjacent_compatible_iff hπ data H m j hj f).mp hA
  have hforward (a b : Fin (j + 1)) (hab : a.val < b.val) (u v : Bool) :
      C (.retained a u) (.retained b v) := by
    by_cases he : a.val + 1 = b.val
    · have hb : b = ⟨a.val + 1, by omega⟩ := Fin.ext he.symm
      rw [hb]
      by_cases huv : u = v
      · subst v
        exact hE a.val (by omega) u
      · exact arithmeticEmptyPullback_compatible
          (arithmeticLabeledAtlas_adjacent_crossLabel_isPullback
            hπ data H m (j + 1) hj a.val (by omega) u v huv) _ _
    · exact TernaryOpenDescent.disjoint_compatible _ _ _ _
        (arithmeticLabeledAtlas_nonadjacent_disjoint
          hπ data m H (j + 1) hj a b (by omega) u v)
  rcases lt_trichotomy a.val b.val with hab | hab | hab
  · exact hforward a b hab u v
  · have he : a = b := Fin.ext hab
    subst b
    by_cases huv : u = v
    · subst v
      exact congrArg (fun t => t ≫ f (.retained a u))
        ((cancel_mono (c (.retained a u))).mp pullback.condition)
    · exact arithmeticEmptyPullback_compatible
        (arithmeticLabeledAtlas_sameDepth_isPullback hπ data H m (j + 1) hj a u v huv) _ _
  · exact TernaryOpenDescent.flip_compatible _ _ _ _ (hforward b a hab v u)

end FLT.Mazur.WeierstrassDividedDepth
