/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteCartesianMarkings

/-!
# Naturality of the original complete markings

Every morphism between specified cartesian squares preserves the lifted labels.
This includes arbitrary further base change and the canonical comparison between
any two realizations of the same fiber square.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.PolygonInfinitesimalStages

set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  {S T Y Z : Scheme}
  (s : S ⟶ Spec (.of (PowerSeries K))) (t : T ⟶ Spec (.of (PowerSeries K)))
  (p : Y ⟶ exactVeroneseProj K n h) (q : Y ⟶ S)
  (hs : IsPullback p q (exactVeroneseProjToBase K n h) s)
  (u : Z ⟶ exactVeroneseProj K n h) (v : Z ⟶ T)
  (ht : IsPullback u v (exactVeroneseProjToBase K n h) t)

/-- A morphism of original cartesian squares preserves every actual labeled marking. -/
@[reassoc] theorem completeCartesianMarking_naturality
    (a : Z ⟶ Y) (b : T ⟶ S) (hb : b ≫ s = t)
    (hp : a ≫ p = u) (hq : a ≫ q = v ≫ b) (i : Fin n) :
    completeCartesianMarking K n h t u v ht i ≫ a =
      b ≫ completeCartesianMarking K n h s p q hs i := by
  apply hs.hom_ext
  · rw [Category.assoc, hp, completeCartesianMarking_fst, Category.assoc,
      completeCartesianMarking_fst, ← Category.assoc, hb]
  · rw [Category.assoc, hq, ← Category.assoc, completeCartesianMarking_snd,
      Category.id_comp, Category.assoc, completeCartesianMarking_snd, Category.comp_id]

/-- The canonical isomorphism between two realizations retains all original markings. -/
@[reassoc] theorem completeCartesianMarking_isoIsPullback
    {Z : Scheme} (u : Z ⟶ exactVeroneseProj K n h) (v : Z ⟶ S)
    (ht : IsPullback u v (exactVeroneseProjToBase K n h) s) (i : Fin n) :
    completeCartesianMarking K n h s p q hs i ≫ (hs.isoIsPullback _ _ ht).hom =
      completeCartesianMarking K n h s u v ht i := by
  apply ht.hom_ext
  · rw [Category.assoc, hs.isoIsPullback_hom_fst, completeCartesianMarking_fst,
      completeCartesianMarking_fst]
  · rw [Category.assoc, hs.isoIsPullback_hom_snd, completeCartesianMarking_snd,
      completeCartesianMarking_snd]

end FLT.Mazur.PolygonInfinitesimalStages
