/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteMarkingNaturality

/-!
# The actual morphism between original polygon fibers under base change

Retain both specified cartesian squares and construct their comparison along
the given base morphism. Its square is cartesian and every original label is
preserved, without choosing or identifying any cubic equation.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  {S T Y Z : Scheme}
  (s : S ⟶ Spec (.of (PowerSeries K))) (t : T ⟶ Spec (.of (PowerSeries K)))
  (p : Y ⟶ exactVeroneseProj K n h) (q : Y ⟶ S)
  (hs : IsPullback p q (exactVeroneseProjToBase K n h) s)
  (r : Z ⟶ exactVeroneseProj K n h) (v : Z ⟶ T)
  (ht : IsPullback r v (exactVeroneseProjToBase K n h) t)
  (b : T ⟶ S) (hb : b ≫ s = t)

/-- The base morphism induces a map between the two retained original squares. -/
def completeCartesianBaseMap : Z ⟶ Y :=
  hs.lift r (v ≫ b) (by rw [Category.assoc, hb]; exact ht.w)

/-- The comparison retains the map to the original polygon total space. -/
@[reassoc] theorem completeCartesianBaseMap_fst :
    completeCartesianBaseMap K n h s t p q hs r v ht b hb ≫ p = r :=
  hs.lift_fst _ _ _

/-- The comparison lies over the specified base morphism. -/
@[reassoc] theorem completeCartesianBaseMap_snd :
    completeCartesianBaseMap K n h s t p q hs r v ht b hb ≫ q = v ≫ b :=
  hs.lift_snd _ _ _

/-- Pullback pasting proves that this particular comparison square is cartesian. -/
theorem completeCartesianBaseMap_isPullback :
    IsPullback (completeCartesianBaseMap K n h s t p q hs r v ht b hb) v q b := by
  have hc : IsPullback r v (exactVeroneseProjToBase K n h) (b ≫ s) := by
    rw [hb]
    exact ht
  exact hc.of_right' hs

/-- Every original labeled marking is retained along the actual comparison. -/
@[reassoc] theorem completeCartesianBaseMap_marking (i : Fin n) :
    completeCartesianMarking K n h t r v ht i ≫
      completeCartesianBaseMap K n h s t p q hs r v ht b hb =
        b ≫ completeCartesianMarking K n h s p q hs i :=
  completeCartesianMarking_naturality K n h s t p q hs r v ht _ b hb
    (completeCartesianBaseMap_fst K n h s t p q hs r v ht b hb)
    (completeCartesianBaseMap_snd K n h s t p q hs r v ht b hb) i

end FLT.Mazur.PolygonInfinitesimalStages
