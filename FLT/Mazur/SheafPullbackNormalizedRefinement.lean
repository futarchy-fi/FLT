/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SheafPullbackObjectwiseRefinement

/-!
# Refinement from normalization equations

Local maps with the prescribed normalization inherit refinement from their
normalized maps. Using equations rather than unfolding local definitions
keeps concrete geometric specializations small for the kernel.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

universe u

namespace FLT.Mazur.SheafPullbackLocalComparison

open AffineIteratedPullbackSections SheafPullbackPathComparison

variable {Z W O X Y : Scheme.{u}}
variable (c : W ⟶ O) (p : O ⟶ X) (q : O ⟶ Y)
variable (i : W ⟶ X) (j : W ⟶ Y) (hi : c ≫ p = i) (hj : c ≫ q = j)
variable (M : X.Modules) (N : Y.Modules)

/-- The normalization equation uniquely determines a transported local map. -/
lemma eq_transport_of_normalize
    (a : (pullback i).obj M ⟶ (pullback j).obj N)
    (A : (pullback c).obj ((pullback p).obj M) ⟶
      (pullback c).obj ((pullback q).obj N))
    (hA : A ≫ (comparison c q j hj).hom.app N =
      (comparison c p i hi).hom.app M ≫ a) :
    A = transport c p q i j hi hj M N a := by
  apply (cancel_mono ((comparison c q j hj).hom.app N)).mp
  rw [hA, transport_normalize]

/-- Refinement follows from normalization at both levels and affine refinement. -/
lemma refine_of_normalize
    (t : Z ⟶ W) (d : Z ⟶ O) (hd : t ≫ c = d)
    (i' : Z ⟶ X) (j' : Z ⟶ Y) (hti : t ≫ i = i') (htj : t ≫ j = j')
    (hi' : d ≫ p = i') (hj' : d ≫ q = j')
    (a : (pullback i).obj M ⟶ (pullback j).obj N)
    (b : (pullback i').obj M ⟶ (pullback j').obj N)
    (A : (pullback c).obj ((pullback p).obj M) ⟶
      (pullback c).obj ((pullback q).obj N))
    (B : (pullback d).obj ((pullback p).obj M) ⟶
      (pullback d).obj ((pullback q).obj N))
    (hA : A ≫ (comparison c q j hj).hom.app N =
      (comparison c p i hi).hom.app M ≫ a)
    (hB : B ≫ (comparison d q j' hj').hom.app N =
      (comparison d p i' hi').hom.app M ≫ b)
    (hab : (pullback t).map a ≫ (compositeIso t j j' htj N).hom =
      (compositeIso t i i' hti M).hom ≫ b) :
    (pullback t).map A ≫ (compositeIso t c d hd ((pullback q).obj N)).hom =
      (compositeIso t c d hd ((pullback p).obj M)).hom ≫ B := by
  rw [eq_transport_of_normalize c p q i j hi hj M N a A hA,
    eq_transport_of_normalize d p q i' j' hi' hj' M N b B hB]
  exact transport_refine_objectwise c p q i j hi hj M N t d hd
    i' j' hti htj hi' hj' a b hab

end FLT.Mazur.SheafPullbackLocalComparison
