/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticLabeledAtlas
public import FLT.Mazur.WeierstrassDividedArithmeticInfinitySeparation
public import FLT.Mazur.WeierstrassSuccessiveArithmeticBranchSeparation

/-!
# Empty intersections in the actual labeled arithmetic cover

Different labels at a single retained depth are disjoint. Every full
positive-depth retained node and the full positive-depth terminal node
miss the original infinity chart at every arithmetic order.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (k : ℕ) (hk : k ≤ n)
local notation "c" => arithmeticLabeledAtlasMap hπ data H m k hk

/-- Different labels of one retained depth have empty full scheme intersection in the atlas. -/
theorem arithmeticLabeledAtlas_sameDepth_isPullback (a : Fin k) (b d : Bool) (hbd : b ≠ d) :
    IsPullback (Scheme.emptyTo _) (Scheme.emptyTo _) (c (.retained a b)) (c (.retained a d)) := by
  have P := arithmeticTensorBranchChart_isPullback_empty π m W (π ^ (start + a.val))
    (data ⟨a.val + 1, by omega⟩).b3 (data ⟨a.val + 1, by omega⟩).b4
    (data ⟨a.val + 1, by omega⟩).b6 H.a1_unit (H.scale a.val) H.a2_div
      (H.b3_div _) (H.b4_div _) (H.b6_div _) b d hbd
  exact IsPullback.of_isLimit (PullbackCone.isLimitOfCompMono _ _
    (arithmeticRetainedTensorChart hπ data m k hk a.val a.isLt) P.cone P.isLimit)

attribute [local irreducible] arithmeticRetainedTensorChart arithmeticLabeledRetainedChart

/-- Index zero is precisely the original infinity tensor chart in arithmetic orientation. -/
theorem arithmeticTensorAtlasMap_infinity :
    arithmeticTensorAtlasMap hπ data m k hk 0 =
      finiteInfinityTensorChart hπ data (Quotient R π m) k hk ≫
        (pullbackSymmetry (Spec.map (CommRingCat.ofHom (algebraMap R (Quotient R π m))))
          (finiteGlobalStructure hπ data k hk)).hom := rfl

/-- The fixed-stage retained tensor index preserves the full positive-depth infinity exclusion. -/
theorem arithmeticRetainedTensorChart_infinity_disjoint (a : ℕ) (ha : a < k)
    (hpos : 0 < start + a) :
    Disjoint (Set.range (arithmeticRetainedTensorChart hπ data m k hk a ha))
      (Set.range (arithmeticTensorAtlasMap hπ data m k hk 0)) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le (show a + 1 ≤ k by omega)
  rw [arithmeticRetainedTensorChart_eq hπ data m (a + 1 + r) hk a ha r hk]
  rw [arithmeticTensorAtlasMap_infinity]
  exact olderArithmetic_infinity_disjoint hπ data m a hpos (by omega) r hk

/-- A full positive-depth retained labeled node misses the original infinity chart. -/
theorem arithmeticLabeledAtlas_retained_infinity_disjoint (a : Fin k) (b : Bool)
    (hpos : 0 < start + a.val) :
    Disjoint (Set.range (c (.retained a b))) (Set.range (c .infinity)) := by
  change Disjoint (Set.range (arithmeticLabeledRetainedChart hπ data H m k hk a b))
    (Set.range (arithmeticTensorAtlasMap hπ data m k hk 0))
  apply (arithmeticRetainedTensorChart_infinity_disjoint
    hπ data m k hk a.val a.isLt hpos).mono_left
  rw [← arithmeticLabeledRetainedChart_image hπ data H m k hk a]
  cases b
  · exact Set.subset_union_left
  · exact Set.subset_union_right

/-- The full positive-depth retained node/infinity intersection is the empty scheme. -/
theorem arithmeticLabeledAtlas_retained_infinity_isPullback (a : Fin k) (b : Bool)
    (hpos : 0 < start + a.val) :
    IsPullback (Scheme.emptyTo _) (Scheme.emptyTo _) (c (.retained a b)) (c .infinity) := by
  let _ := Scheme.isEmpty_pullback (c (.retained a b)) (c .infinity)
    (arithmeticLabeledAtlas_retained_infinity_disjoint hπ data H m k hk a b hpos)
  apply IsPullback.of_iso_pullback ⟨Scheme.empty_ext _ _⟩
    (asIso (Scheme.emptyTo (pullback (c (.retained a b)) (c .infinity))))
  · exact Scheme.empty_ext _ _
  · exact Scheme.empty_ext _ _

/-- Normalizing the terminal chart does not introduce any positive-depth infinity intersection. -/
theorem arithmeticLabeledAtlas_terminal_infinity_disjoint (hpos : 0 < start + k) :
    Disjoint (Set.range (c .terminal)) (Set.range (c .infinity)) := by
  change Disjoint (Set.range (arithmeticLabeledTerminalChart hπ data H m k hk)) _
  rw [arithmeticLabeledTerminalChart_image]
  exact terminalArithmetic_infinity_disjoint hπ data m k hk hpos

/-- The entire normalized positive-depth terminal/infinity fiber product is empty. -/
theorem arithmeticLabeledAtlas_terminal_infinity_isPullback (hpos : 0 < start + k) :
    IsPullback (Scheme.emptyTo _) (Scheme.emptyTo _) (c .terminal) (c .infinity) := by
  let _ := Scheme.isEmpty_pullback (c .terminal) (c .infinity)
    (arithmeticLabeledAtlas_terminal_infinity_disjoint hπ data H m k hk hpos)
  apply IsPullback.of_iso_pullback ⟨Scheme.empty_ext _ _⟩
    (asIso (Scheme.emptyTo (pullback (c .terminal) (c .infinity))))
  · exact Scheme.empty_ext _ _
  · exact Scheme.empty_ext _ _

end FLT.Mazur.WeierstrassDividedDepth
