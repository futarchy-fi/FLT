/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticLabeledAtlas
public import FLT.Mazur.WeierstrassDividedArithmeticInitialSeparation

/-!
# The first edges of the full labeled arithmetic cover

The initial D(p) attaches to the first retained branch of the same label,
with the original corrected Laurent comparison. The opposite label has
empty intersection. This edge is distinct from the initial D(q) overlap.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (k : ℕ) (hk : k ≤ n) (hpos : 0 < k)
local notation "Q" => Quotient R π m
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "c" => arithmeticLabeledAtlasMap hπ data H m k hk
local notation "P" => arithmeticInitialPunctureInclusion π m W (π ^ start) H.a1_unit H.scale_div
local notation "E" => arithmeticInitialPunctureIso π m W (π ^ start)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit H.scale_div H.a2_div
    (H.b3_div _) (H.b4_div _) (H.b6_div _)

/-- Each initial label attaches along the full standard D(p) to its first retained branch. -/
theorem arithmeticLabeledAtlas_initial_edge_isPullback (b : Bool) :
    IsPullback P ((E).inv ≫ PolygonSmoothing.rightBranchOpen Q (parameter R π m))
      (c (.initial b)) (c (.retained ⟨0, hpos⟩ b)) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le (show 1 ≤ k by omega)
  dsimp only [arithmeticLabeledAtlasMap, arithmeticLabeledInitialChart,
    arithmeticLabeledRetainedChart]
  rw [arithmeticRetainedTensorChart_eq hπ data m (1 + r) hk 0 hpos r hk]
  exact initialArithmeticStandardPuncture_isPullback hπ data m (by omega) r hk
    H.a1_unit H.scale_div H.a2_div (H.b3_div _) (H.b4_div _) (H.b6_div _)
      (H.b3_div _) (H.b4_div _) (H.b6_div _) b

/-- The standard first edge preserves the original corrected Laurent parameter on both charts. -/
@[reassoc] theorem arithmeticLabeledAtlas_initial_edge_overlap (b : Bool) :
    P ≫ c (.initial b) =
      ((E).inv ≫ PolygonSmoothing.rightBranchOpen Q (parameter R π m)) ≫
        c (.retained ⟨0, hpos⟩ b) :=
  (arithmeticLabeledAtlas_initial_edge_isPullback hπ data H m k hk hpos b).w

/-- The first edge cannot connect an initial node to the other retained label. -/
theorem arithmeticLabeledAtlas_initial_crossLabel_isPullback (b other : Bool) (hbd : b ≠ other) :
    IsPullback (Scheme.emptyTo _) (Scheme.emptyTo _)
      (c (.initial b)) (c (.retained ⟨0, hpos⟩ other)) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le (show 1 ≤ k by omega)
  dsimp only [arithmeticLabeledAtlasMap, arithmeticLabeledInitialChart,
    arithmeticLabeledRetainedChart]
  rw [arithmeticRetainedTensorChart_eq hπ data m (1 + r) hk 0 hpos r hk]
  exact initialArithmeticNodes_crossLabel_isPullback hπ data m (by omega) r hk
    H.a1_unit H.scale_div H.a2_div (H.b3_div _) (H.b4_div _) (H.b6_div _)
      (H.b3_div _) (H.b4_div _) (H.b6_div _) b other hbd

end FLT.Mazur.WeierstrassDividedDepth
