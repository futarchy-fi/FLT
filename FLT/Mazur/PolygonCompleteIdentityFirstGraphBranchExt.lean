/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFirstGraphBranchMaps
public import FLT.Mazur.SurjectiveDominantEpi
public import FLT.Mazur.ChowProductOpenGluing

/-!
# The two original punctures detect morphisms of the finite graph

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
attribute [local irreducible] completeIdentityFirstActionUnit completeIdentityFirstActionField
  completeIdentityFirstActionNodeDefect completeIdentityFirstErrorAlgebra
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "S" => Ring K[T;T⁻¹] 1
local notation "L" => (S)[T;T⁻¹]
local notation "E" => completeIdentityFirstErrorAlgebra K n h i

/-- The two original Laurent branches together map to the full finite graph. -/
def completeIdentityFirstGraphBothBranches :
    Spec (.of ((L) × (L))) ⟶ completeIdentityFirstGraphScheme K n h i :=
  Spec.map (CommRingCat.ofHom ((E).restrictScalars (S)).val.toRingHom)

/-- These punctures detect all functions, including nilpotents of the finite graph. -/
instance completeIdentityFirstGraphBothBranches_schematic :
    IsSchemeTheoreticallyDominant (completeIdentityFirstGraphBothBranches K n h i) :=
  SurjectiveDominantEpi.spec_schematic _ Subtype.val_injective

/-- The first product summand is exactly the original left graph branch. -/
@[reassoc] theorem completeIdentityFirstGraphBothBranches_left :
    Spec.map (CommRingCat.ofHom (RingHom.fst (L) (L))) ≫
      completeIdentityFirstGraphBothBranches K n h i =
        completeIdentityFirstGraphLeftBranch K n h i := by
  rw [completeIdentityFirstGraphBothBranches, ← Spec.map_comp]
  rfl

/-- The second product summand is exactly the original right graph branch. -/
@[reassoc] theorem completeIdentityFirstGraphBothBranches_right :
    Spec.map (CommRingCat.ofHom (RingHom.snd (L) (L))) ≫
      completeIdentityFirstGraphBothBranches K n h i =
        completeIdentityFirstGraphRightBranch K n h i := by
  rw [completeIdentityFirstGraphBothBranches, ← Spec.map_comp]
  rfl

/-- Two original branch comparisons prove equality on the entire finite graph. -/
theorem completeIdentityFirstGraph_ext {Y B : Scheme} (s : Y ⟶ B) [IsSeparated s]
    (f g : completeIdentityFirstGraphScheme K n h i ⟶ Y) (hb : f ≫ s = g ≫ s)
    (hl : completeIdentityFirstGraphLeftBranch K n h i ≫ f =
      completeIdentityFirstGraphLeftBranch K n h i ≫ g)
    (hr : completeIdentityFirstGraphRightBranch K n h i ≫ f =
      completeIdentityFirstGraphRightBranch K n h i ≫ g) : f = g := by
  apply Chow.schematicallyDense_ext s hb (completeIdentityFirstGraphBothBranches K n h i)
  apply (cancel_epi (coprodSpec (L) (L))).mp
  apply coprod.hom_ext
  · simpa only [Category.assoc, coprodSpec_inl_assoc,
      completeIdentityFirstGraphBothBranches_left_assoc] using hl
  · simpa only [Category.assoc, coprodSpec_inr_assoc,
      completeIdentityFirstGraphBothBranches_right_assoc] using hr

end FLT.Mazur.PolygonInfinitesimalStages
