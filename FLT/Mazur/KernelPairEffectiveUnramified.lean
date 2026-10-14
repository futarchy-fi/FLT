/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.KernelPairEffectiveOpenEtale
public import FLT.Mazur.KernelPairEtaleUnramified
public import FLT.Mazur.SchemeFppfTargetOpen

/-!
# Constructed unramified and etale effective regions

The entire source above the intrinsic effective target is formally unramified.
Its constructed fppf restriction is therefore etale. Neither flatness nor
unramifiedness is assumed for the original candidate projection.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.KernelPairEffectiveOpen
variable {D A T : Scheme.{u}} (p q : D ⟶ A) (w : A ⟶ T) (h : p ≫ w = q ≫ w)
  [Mono (pullback.lift p q h)] [Etale p]

/-- Original etale arrows force unramified geometry on the full effective source. -/
theorem projection_formallyUnramified : FormallyUnramified (projection p q w h) :=
  KernelPairEtaleGeometry.formallyUnramified (fst p q w h) (snd p q w h)
    (projection p q w h) (isPullback p q w h)

/-- Any actual flat effective projection is etale, without a surjectivity premise. -/
theorem projection_etale_of_flat [Flat (projection p q w h)]
    [LocallyOfFinitePresentation w] : Etale (projection p q w h) := by
  let _ := projection_formallyUnramified p q w h
  exact Etale.of_formallyUnramified_of_flat _

/-- The intrinsic fppf region has an etale projection, even for an arbitrary original model. -/
theorem fppfProjection_etale [LocallyOfFinitePresentation w] :
    Etale (SchemeFppfTargetOpen.projection (projection p q w h)) := by
  let _ := projection_formallyUnramified p q w h
  let _ : FormallyUnramified (SchemeFppfTargetOpen.projection (projection p q w h)) :=
    MorphismProperty.of_isPullback
      (SchemeFppfTargetOpen.isPullback (projection p q w h)) inferInstance
  exact Etale.of_formallyUnramified_of_flat _

end FLT.Mazur.KernelPairEffectiveOpen
