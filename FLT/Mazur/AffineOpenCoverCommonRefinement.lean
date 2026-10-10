/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineOpenOverlapCover

/-!
# Common affine refinements over an arbitrary scheme

Take an affine open cover of the actual fiber product of two overlap charts.
Its members refine both charts and cover their intersection, without assuming
that this intersection is affine. Both coordinate triangles commute.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.AffineOpenCoverCommonRefinement
variable {X : Scheme.{u}}
variable {A B : CommRingCat.{u}}
variable (f : Spec A ⟶ X) (g : Spec B ⟶ X)

/-- Affine charts covering the geometric intersection of two independent overlap charts. -/
def commonCover : (Limits.pullback f g).AffineOpenCover :=
  (Limits.pullback f g).affineOpenCover

variable (i : (commonCover f g).I₀)

/-- Coordinates of the common refinement in the first overlap chart. -/
def commonLeft : A ⟶ (commonCover f g).X i :=
  Spec.preimage ((commonCover f g).f i ≫ Limits.pullback.fst f g)

/-- Coordinates of the common refinement in the second overlap chart. -/
def commonRight : B ⟶ (commonCover f g).X i :=
  Spec.preimage ((commonCover f g).f i ≫ Limits.pullback.snd f g)

/-- The common affine chart mapped into the original geometric overlap. -/
def commonMap :
    Spec ((commonCover f g).X i) ⟶ X :=
  (commonCover f g).f i ≫ Limits.pullback.fst f g ≫ f

/-- The first triangle into the geometric overlap commutes. -/
theorem commonLeft_over :
    Spec.map (commonLeft f g i) ≫ f =
      commonMap f g i := by
  simp only [commonLeft, commonMap, Spec.map_preimage,
    Category.assoc]

/-- The independent second triangle has the same map into the overlap. -/
theorem commonRight_over :
    Spec.map (commonRight f g i) ≫ g =
      commonMap f g i := by
  simp only [commonRight, commonMap, Spec.map_preimage,
    Category.assoc, Limits.pullback.condition]

/-- The common refinement charts cover the entire intersection of the two charts. -/
theorem commonCover_covers (x : (Limits.pullback f g : Scheme.{u})) :
    ∃ i, x ∈ Set.range ((commonCover f g).f i) :=
  ⟨(commonCover f g).idx x,
    (commonCover f g).covers x⟩

/-- For open overlap charts, common refinement remains open in the first chart. -/
instance commonLeft_isOpenImmersion [IsOpenImmersion g] :
    IsOpenImmersion (Spec.map (commonLeft f g i)) := by
  dsimp only [commonLeft]
  rw [Spec.map_preimage]
  infer_instance

/-- For open overlap charts, common refinement remains open in the second chart. -/
instance commonRight_isOpenImmersion [IsOpenImmersion f] :
    IsOpenImmersion (Spec.map (commonRight f g i)) := by
  dsimp only [commonRight]
  rw [Spec.map_preimage]
  infer_instance

/-- Each common chart is an open immersion into the ambient scheme. -/
instance commonMap_isOpenImmersion [IsOpenImmersion f] [IsOpenImmersion g] :
    IsOpenImmersion (commonMap f g i) := by
  dsimp only [commonMap]
  infer_instance

/-- Common affine charts cover the intersection of the two open images. -/
theorem commonMap_covers [IsOpenImmersion f] [IsOpenImmersion g] (x : X)
    (hx : x ∈ f.opensRange ⊓ g.opensRange) :
    ∃ i, x ∈ (commonMap f g i).opensRange := by
  have hx' : x ∈ Set.range (Limits.pullback.fst f g ≫ f) := by
    rw [IsOpenImmersion.range_pullback_to_base_of_left]
    exact hx
  obtain ⟨y, rfl⟩ := hx'
  obtain ⟨i, z, hz⟩ := commonCover_covers f g y
  refine ⟨i, z, ?_⟩
  change (Limits.pullback.fst f g ≫ f) ((commonCover f g).f i z) = _
  rw [hz]

end FLT.Mazur.AffineOpenCoverCommonRefinement
