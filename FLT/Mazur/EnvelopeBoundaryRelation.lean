/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.InvariantBoundaryPullback
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# The full relation on an invariant closed boundary

Pulling back one endpoint already restricts both endpoints scheme-theoretically.
The second endpoint is also Cartesian, so both smooth or etale endpoint
properties survive. Every original arrow with a closed first endpoint lifts,
without reducing its test scheme or choosing a translation branch.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.SchemeOpenEnvelope
universe u
set_option backward.isDefEq.respectTransparency false
variable {Y X Z : Scheme.{u}} (π : Y ⟶ X) (O : Y.Opens)
  [IsAffine X] [IsLocallyNoetherian X]
  (a b : Z ⟶ X) [Smooth a] [Smooth b]
  (h : a ⁻¹ᵁ fullFiberInterior π O = b ⁻¹ᵁ fullFiberInterior π O)
local notation "j" => Scheme.IdealSheafData.subschemeι (boundaryIdealSheaf π O)

/-- The second endpoint on the actual first-endpoint closed pullback. -/
def boundaryRelationSnd : pullback a j ⟶ (boundaryIdealSheaf π O).subscheme :=
  (boundaryPullbackIso π O a b h).hom ≫ pullback.snd b j

/-- The second endpoint retains the original whole relation arrow. -/
@[reassoc]
theorem boundaryRelationSnd_comp :
    boundaryRelationSnd π O a b h ≫ j = pullback.fst a j ≫ b := by
  rw [boundaryRelationSnd, Category.assoc, ← pullback.condition,
    ← Category.assoc, boundaryPullbackIso_fst]

/-- Restriction at the first endpoint is also restriction at the second endpoint. -/
theorem boundaryRelationSnd_isPullback :
    IsPullback (pullback.fst a j) (boundaryRelationSnd π O a b h) b j :=
  IsPullback.of_iso_pullback ⟨(boundaryRelationSnd_comp π O a b h).symm⟩
    (boundaryPullbackIso π O a b h) (boundaryPullbackIso_fst π O a b h) rfl

/-- The second closed endpoint is smooth over the actual closed source. -/
instance boundaryRelationSnd_smooth : Smooth (boundaryRelationSnd π O a b h) :=
  MorphismProperty.of_isPullback (boundaryRelationSnd_isPullback π O a b h)
    (inferInstanceAs (Smooth b))

/-- Etale original endpoints stay etale on the full closed restriction. -/
instance boundaryRelationSnd_etale [Etale b] : Etale (boundaryRelationSnd π O a b h) :=
  MorphismProperty.of_isPullback (boundaryRelationSnd_isPullback π O a b h)
    (inferInstanceAs (Etale b))

/-- Lifting the first endpoint automatically retains any given second closed endpoint. -/
theorem boundaryRelation_lift_snd {T : Scheme.{u}} (z : T ⟶ Z)
    (x y : T ⟶ (boundaryIdealSheaf π O).subscheme)
    (hx : z ≫ a = x ≫ j) (hy : z ≫ b = y ≫ j) :
    pullback.lift z x hx ≫ boundaryRelationSnd π O a b h = y := by
  apply (cancel_mono j).mp
  rw [Category.assoc, boundaryRelationSnd_comp, pullback.lift_fst_assoc, hy]

/-- All original arrows with closed endpoints have a unique full closed lift. -/
theorem boundaryRelation_lift {T : Scheme.{u}} (z : T ⟶ Z)
    (x y : T ⟶ (boundaryIdealSheaf π O).subscheme)
    (hx : z ≫ a = x ≫ j) (hy : z ≫ b = y ≫ j) :
    ∃! w : T ⟶ pullback a j, w ≫ pullback.fst a j = z ∧
      w ≫ pullback.snd a j = x ∧ w ≫ boundaryRelationSnd π O a b h = y := by
  refine ⟨pullback.lift z x hx, ⟨pullback.lift_fst _ _ _, pullback.lift_snd _ _ _,
    boundaryRelation_lift_snd π O a b h z x y hx hy⟩, ?_⟩
  intro w hw
  exact pullback.hom_ext (hw.1.trans (pullback.lift_fst _ _ _).symm)
    (hw.2.1.trans (pullback.lift_snd _ _ _).symm)

end FLT.Mazur.SchemeOpenEnvelope
