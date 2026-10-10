/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffinePullbackNormalization
public import FLT.Mazur.SheafPullbackLocalComparison

/-!
# Refinement with objectwise pullback comparisons

Keep composition comparisons objectwise while transporting local maps.
The conversion to natural path comparisons is checked with abstract
schemes, avoiding expansion of concrete coefficient sheaves in consumers.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

universe u

namespace FLT.Mazur.SheafPullbackLocalComparison

open AffineIteratedPullbackSections

variable {Z W O X Y : Scheme.{u}}

/-- Objectwise normalized refinement implies refinement of the transported overlap maps. -/
lemma transport_refine_objectwise
    (c : W ⟶ O) (p : O ⟶ X) (q : O ⟶ Y)
    (i : W ⟶ X) (j : W ⟶ Y) (hi : c ≫ p = i) (hj : c ≫ q = j)
    (M : X.Modules) (N : Y.Modules)
    (t : Z ⟶ W) (d : Z ⟶ O) (hd : t ≫ c = d)
    (i' : Z ⟶ X) (j' : Z ⟶ Y) (hti : t ≫ i = i') (htj : t ≫ j = j')
    (hi' : d ≫ p = i') (hj' : d ≫ q = j')
    (a : (pullback i).obj M ⟶ (pullback j).obj N)
    (b : (pullback i').obj M ⟶ (pullback j').obj N)
    (hab : (pullback t).map a ≫ (compositeIso t j j' htj N).hom =
      (compositeIso t i i' hti M).hom ≫ b) :
    (pullback t).map (transport c p q i j hi hj M N a) ≫
        (compositeIso t c d hd ((pullback q).obj N)).hom =
      (compositeIso t c d hd ((pullback p).obj M)).hom ≫
        transport d p q i' j' hi' hj' M N b := by
  simp only [compositeIso_eq_comparison, Iso.app_hom] at hab ⊢
  exact transport_refine c p q i j hi hj M N t d hd i' j' hti htj hi' hj' a b hab

end FLT.Mazur.SheafPullbackLocalComparison
