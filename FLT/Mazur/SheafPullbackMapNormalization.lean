/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SheafPullbackPathComparison

/-!
# Normalizing pullbacks of overlap maps

Pulling back a map between two coordinate sheaves and normalizing both
paths commutes with further pullback. The proof uses pseudofunctor coherence.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

universe u

namespace FLT.Mazur.SheafPullbackMapNormalization

open SheafPullbackPathComparison

variable {Z W O X Y : Scheme.{u}}
variable (c : W ⟶ O) (p : O ⟶ X) (q : O ⟶ Y)
variable (i : W ⟶ X) (j : W ⟶ Y) (hi : c ≫ p = i) (hj : c ≫ q = j)
variable {M : X.Modules} {N : Y.Modules}

/-- Normalize the pullback of a map between two coordinate sheaves. -/
def normalize (a : (pullback p).obj M ⟶ (pullback q).obj N) :
    (pullback i).obj M ⟶ (pullback j).obj N :=
  (comparison c p i hi).inv.app M ≫ (pullback c).map a ≫
    (comparison c q j hj).hom.app N

/-- Normalization is conjugation by the two path comparisons. -/
@[reassoc]
lemma normalize_comm (a : (pullback p).obj M ⟶ (pullback q).obj N) :
    (comparison c p i hi).hom.app M ≫ normalize c p q i j hi hj a =
      (pullback c).map a ≫ (comparison c q j hj).hom.app N := by
  simp only [normalize, Iso.hom_inv_id_app_assoc]

/-- A normalized pullback of an isomorphism is invertible. -/
instance normalize_isIso (a : (pullback p).obj M ⟶ (pullback q).obj N) [IsIso a] :
    IsIso (normalize c p q i j hi hj a) := by
  unfold normalize
  infer_instance

/-- Normalized overlap maps commute with any further pullback. -/
lemma normalize_refine (t : Z ⟶ W) (d : Z ⟶ O) (hd : t ≫ c = d)
    (i' : Z ⟶ X) (j' : Z ⟶ Y) (hti : t ≫ i = i') (htj : t ≫ j = j')
    (hi' : d ≫ p = i') (hj' : d ≫ q = j')
    (a : (pullback p).obj M ⟶ (pullback q).obj N) :
    (pullback t).map (normalize c p q i j hi hj a) ≫
        (comparison t j j' htj).hom.app N =
      (comparison t i i' hti).hom.app M ≫ normalize d p q i' j' hi' hj' a := by
  apply (cancel_epi ((pullback t).map ((comparison c p i hi).hom.app M))).mp
  rw [← Functor.map_comp_assoc, normalize_comm, Functor.map_comp, Category.assoc]
  rw [comparison_assoc t c q d j j' hd hj htj hj']
  have hn := (comparison t c d hd).hom.naturality a
  dsimp only [Functor.comp_map] at hn
  rw [← Category.assoc, hn]
  rw [Category.assoc, ← normalize_comm d p q i' j' hi' hj']
  rw [← Category.assoc, ← comparison_assoc t c p d i i' hd hi hti hi', Category.assoc]

end FLT.Mazur.SheafPullbackMapNormalization
