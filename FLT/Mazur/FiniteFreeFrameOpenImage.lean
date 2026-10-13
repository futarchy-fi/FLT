/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LocallyFiniteFreeOpenCover

/-!
# Transporting exact-rank frames through open immersions

A frame around a point of an open pullback gives a frame of the original
sheaf around the image point, with the identical coordinate index type.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {X Y : Scheme.{0}} (M : X.Modules) (f : Y ⟶ X) [IsOpenImmersion f]

/-- An exact frame on an open pullback transports to its actual open image. -/
theorem frame_of_openPullback {ι : Type} (y : Y) (V : Y.Opens) (hy : y ∈ V)
    (e : ((pullback f).obj M).restrict V.ι ≅ SheafOfModules.free ι) :
    ∃ U : X.Opens, f y ∈ U ∧ Nonempty (M.restrict U.ι ≅ SheafOfModules.free ι) := by
  let j := V.ι ≫ f
  let a := (restrictFunctorComp V.ι f).app M ≪≫
    (restrictFunctor V.ι).mapIso ((restrictFunctorIsoPullback f).app M) ≪≫ e
  let b := (restrictFunctorComp j.isoOpensRange.inv j).symm ≪≫
    restrictFunctorCongr j.isoOpensRange_inv_comp
  refine ⟨j.opensRange, ⟨⟨y, hy⟩, rfl⟩, ⟨?_⟩⟩
  exact (b.app M).symm ≪≫ (restrictFunctor j.isoOpensRange.inv).mapIso a ≪≫
    (restrictFunctorIsoPullback j.isoOpensRange.inv).app _ ≪≫
      ModuleGlobalEvaluationPullback.freeIso j.isoOpensRange.inv ι

end FLT.Mazur.FCurve
