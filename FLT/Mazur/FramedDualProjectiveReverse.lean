/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FramedDualProjectivePullback
public import FLT.Mazur.LocallySplitLineAmbientTransport

/-!
# Reverse-section square in pulled ambient frames

The reverse point of an actual locally split line commutes with the constructed
geometric projective map. The source line may be nontrivial on the affine base.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.FramedDualProjectivePullback
open FCurve SplitLineAffineNeighborhood FiniteFreePullbackFrame
open SplitLineAffinePresentation DualFreeSheafCoordinates
variable {X Y : Scheme.{u}} [IsAffine X] (f : X ⟶ Y)
variable {L M : Y.Modules} (s : L ⟶ M)
variable (hL : LocallyFreeRankOne L) (hs : LocallySplit s)
variable {ι κ : Type u} [Finite ι] [Finite κ]
variable (e : M ≅ SheafOfModules.free ι)
variable (d : (pullback f).obj M ≅ SheafOfModules.free κ)

omit [IsAffine X] [Finite ι] [Finite κ] in
/-- The original pulled inclusion has the claimed coordinates in any pulled frame. -/
lemma pulled_inclusion :
    ((pullback f).map s ≫ d.hom) ≫ (d.symm ≪≫ frame f e).hom =
      SplitSheafLinePullback.inclusion f (s ≫ e.hom) := by
  simp only [Iso.trans_hom, Iso.symm_hom, frame, Functor.mapIso_hom,
    SplitSheafLinePullback.inclusion, Functor.map_comp,
    Category.assoc, Iso.hom_inv_id_assoc]

/-- The actual reverse-section square commutes for arbitrary finite free ambient frames. -/
lemma reverse_square :
    f ≫ morphism (s ≫ e.hom) hL (hs.postcompose s e) =
      morphism ((pullback f).map s ≫ d.hom) (hL.pullback f)
        ((hs.pullback s f).postcompose _ d) ≫ map f e d := by
  rw [morphism_pullback, map, ← Category.assoc]
  have hp := morphism_ambientIso ((pullback f).map s ≫ d.hom) (hL.pullback f)
    ((hs.pullback s f).postcompose _ d) (d.symm ≪≫ frame f e)
  change _ ≫ (projectiveIso (d.symm ≪≫ frame f e)).hom = _ at hp
  rw [hp]
  congr 2
  exact (pulled_inclusion f s e d).symm

end FLT.Mazur.FramedDualProjectivePullback
