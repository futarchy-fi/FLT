/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonTopNodeGraphBranchMaps
public import FLT.Mazur.SurjectiveDominantEpi
public import FLT.Mazur.ChowProductOpenGluing

/-!
# The two original punctures detect morphisms of the higher graph

The embedding of the graph algebra into the two Laurent rings makes their
combined spectrum schematically dominant. Equality on both original branches
therefore detects whole-graph morphisms to separated targets, with nilpotents.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (R : Type) [CommRing R] (m : ℕ)
variable (u v : ((Ring R (m + 1))[T;T⁻¹])ˣ)
local notation "S" => Ring R (m + 1)
local notation "L" => (S)[T;T⁻¹]
local notation "E" => topNodeGraphAlgebra R m u v

/-- The first product summand is exactly the original left graph branch. -/
@[reassoc] theorem topNodeGraphBranches_left :
    Spec.map (CommRingCat.ofHom (RingHom.fst (L) (L))) ≫
      topNodeGraphBranches R m u v =
        topNodeGraphLeftBranch R m u v := by
  rw [topNodeGraphBranches, ← Spec.map_comp]
  rfl

/-- The second product summand is exactly the original right graph branch. -/
@[reassoc] theorem topNodeGraphBranches_right :
    Spec.map (CommRingCat.ofHom (RingHom.snd (L) (L))) ≫
      topNodeGraphBranches R m u v =
        topNodeGraphRightBranch R m u v := by
  rw [topNodeGraphBranches, ← Spec.map_comp]
  rfl

/-- Two original branch comparisons prove equality on the entire higher graph. -/
theorem topNodeGraph_ext {Y B : Scheme} (s : Y ⟶ B) [IsSeparated s]
    (f g : topNodeGraphScheme R m u v ⟶ Y) (hb : f ≫ s = g ≫ s)
    (hl : topNodeGraphLeftBranch R m u v ≫ f =
      topNodeGraphLeftBranch R m u v ≫ g)
    (hr : topNodeGraphRightBranch R m u v ≫ f =
      topNodeGraphRightBranch R m u v ≫ g) : f = g := by
  apply Chow.schematicallyDense_ext s hb (topNodeGraphBranches R m u v)
  apply (cancel_epi (coprodSpec (L) (L))).mp
  apply coprod.hom_ext
  · simpa only [Category.assoc, coprodSpec_inl_assoc,
      topNodeGraphBranches_left_assoc] using hl
  · simpa only [Category.assoc, coprodSpec_inr_assoc,
      topNodeGraphBranches_right_assoc] using hr

end FLT.Mazur.PolygonInfinitesimalStages
