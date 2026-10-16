/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticRetainedPolygon
public import FLT.Mazur.WeierstrassDividedArithmeticLabeledSystem
public import FLT.Mazur.WeierstrassDividedArithmeticLabeledAdjacent
public import FLT.Mazur.PolygonArithmeticSystem

/-!
# Specific retained comparison systems and original intersection equations

The constructed local polygon maps form natural transformations on the original
labeled quotient systems. Their edge equations hold on the actual fiber products.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (H : ArithmeticAtlasCoefficients data) (k : ℕ) (hk : k ≤ n)

/-- Each original retained label has a specific comparison to the full polygon system. -/
def arithmeticRetainedPolygonSystem (a : Fin k) (b : Bool) :
    arithmeticLabeledChartSystem hπ data H k hk (.retained a b) ⟶
      stageSystem R π (2 * k + 3) (by omega) :=
  NatTrans.ofSequence (fun m => arithmeticRetainedPolygonMap hπ data H m k hk a b) (by
    intro m
    simpa only [arithmeticLabeledChartSystem, stageSystem, Functor.ofSequence_obj,
      Functor.ofSequence_map_homOfLE_succ] using
        arithmeticRetainedPolygonMap_restriction hπ data H m k hk a b)

omit [IsBezout R] in
/-- The specific comparison preserves every original quotient arrow, including skipped orders. -/
@[reassoc] theorem arithmeticRetainedPolygonSystem_naturality
    (a : Fin k) (b : Bool) {l m : ℕ} (hlm : l ≤ m) :
    (arithmeticLabeledChartSystem hπ data H k hk (.retained a b)).map (homOfLE hlm) ≫
      arithmeticRetainedPolygonMap hπ data H m k hk a b =
    arithmeticRetainedPolygonMap hπ data H l k hk a b ≫
      (stageSystem R π (2 * k + 3) (by omega)).map (homOfLE hlm) :=
  (arithmeticRetainedPolygonSystem hπ data H k hk a b).naturality (homOfLE hlm)

/-- The actual full adjacent fiber products satisfy the specific polygon comparison equation. -/
theorem arithmeticRetainedPolygonMap_overlap (m a : ℕ) (ha : a + 1 < k) (b : Bool) :
    pullback.fst
      (arithmeticLabeledAtlasMap hπ data H m k hk (.retained ⟨a, by omega⟩ b))
      (arithmeticLabeledAtlasMap hπ data H m k hk (.retained ⟨a + 1, ha⟩ b)) ≫
        arithmeticRetainedPolygonMap hπ data H m k hk ⟨a, by omega⟩ b =
    pullback.snd
      (arithmeticLabeledAtlasMap hπ data H m k hk (.retained ⟨a, by omega⟩ b))
      (arithmeticLabeledAtlasMap hπ data H m k hk (.retained ⟨a + 1, ha⟩ b)) ≫
        arithmeticRetainedPolygonMap hπ data H m k hk ⟨a + 1, ha⟩ b := by
  have T := arithmeticLabeledAtlas_adjacent_isPullback hπ data H m k hk a ha b
  rw [← cancel_epi T.isoPullback.hom]
  simp only [← Category.assoc, IsPullback.isoPullback_hom_fst,
    IsPullback.isoPullback_hom_snd]
  exact arithmeticRetainedPolygonMap_adjacent hπ data H m k hk a ha b

end FLT.Mazur.WeierstrassDividedDepth
