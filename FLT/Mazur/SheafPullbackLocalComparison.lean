/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SheafPullbackPathComparison

/-!
# Transporting local comparisons to an overlap

A comparison on a chart becomes a map between the restrictions of two
fixed sheaves on an overlap. Refinement compatibility survives this
transport by associativity of the actual pullback functors.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

universe u

namespace FLT.Mazur.SheafPullbackLocalComparison

open SheafPullbackPathComparison

variable {Z W O X Y : Scheme.{u}}
variable (c : W ⟶ O) (p : O ⟶ X) (q : O ⟶ Y)
variable (i : W ⟶ X) (j : W ⟶ Y) (hi : c ≫ p = i) (hj : c ≫ q = j)
variable (M : X.Modules) (N : Y.Modules)

/-- Regard a normalized chart comparison as a map of restricted overlap sheaves. -/
def transport (a : (pullback i).obj M ⟶ (pullback j).obj N) :
    (pullback c).obj ((pullback p).obj M) ⟶
      (pullback c).obj ((pullback q).obj N) :=
  (comparison c p i hi).hom.app M ≫ a ≫ (comparison c q j hj).inv.app N

/-- The transported comparison retains its original normalization. -/
@[reassoc]
lemma transport_normalize (a : (pullback i).obj M ⟶ (pullback j).obj N) :
    transport c p q i j hi hj M N a ≫ (comparison c q j hj).hom.app N =
      (comparison c p i hi).hom.app M ≫ a := by
  simp only [transport, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]

/-- Invertible local comparisons stay invertible after normalization. -/
instance transport_isIso (a : (pullback i).obj M ⟶ (pullback j).obj N) [IsIso a] :
    IsIso (transport c p q i j hi hj M N a) := by
  unfold transport
  infer_instance

/-- Transported maps commute with refinement whenever the normalized maps do. -/
lemma transport_refine (t : Z ⟶ W) (d : Z ⟶ O) (hd : t ≫ c = d)
    (i' : Z ⟶ X) (j' : Z ⟶ Y) (hti : t ≫ i = i') (htj : t ≫ j = j')
    (hi' : d ≫ p = i') (hj' : d ≫ q = j')
    (a : (pullback i).obj M ⟶ (pullback j).obj N)
    (b : (pullback i').obj M ⟶ (pullback j').obj N)
    (hab : (pullback t).map a ≫ (comparison t j j' htj).hom.app N =
      (comparison t i i' hti).hom.app M ≫ b) :
    (pullback t).map (transport c p q i j hi hj M N a) ≫
        (comparison t c d hd).hom.app ((pullback q).obj N) =
      (comparison t c d hd).hom.app ((pullback p).obj M) ≫
        transport d p q i' j' hi' hj' M N b := by
  apply (cancel_mono ((comparison d q j' hj').hom.app N)).mp
  rw [Category.assoc, Category.assoc, transport_normalize]
  rw [← comparison_assoc t c q d j j' hd hj htj hj' N]
  rw [← Category.assoc, ← Functor.map_comp, transport_normalize,
    Functor.map_comp, Category.assoc, hab, ← Category.assoc,
    comparison_assoc t c p d i i' hd hi hti hi' M, Category.assoc]

end FLT.Mazur.SheafPullbackLocalComparison
