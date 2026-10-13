/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
public import Mathlib.CategoryTheory.Comma.Over.Pullback

/-!
# Detecting quotient geometry from its full kernel pair

An fppf cover of the target may factor through the source without the source
projection itself being known to be fppf. Pulling its full kernel pair back
along this factorization detects geometric properties of the projection.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.RelativeKernelPairPropertyDescent
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme.{u}} {A U W Z : Over S} {p q : A ⟶ U}
  (δ : U ⟶ Z) (H : IsPullback p q δ δ) (g : W ⟶ U)

include H

/-- Refining only one endpoint gives the pullback along the actual composite cover. -/
theorem refinedKernelSquare :
    IsPullback (pullback.fst g p) (pullback.snd g p ≫ q) (g ≫ δ) δ :=
  (IsPullback.of_hasPullback g p).paste_vert H

/-- Properties local for fppf target covers are detected by the full kernel relation. -/
theorem property (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange]
    [P.DescendsAlong (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation)]
    (hp : P p.left) [Flat (g ≫ δ).left] [Surjective (g ≫ δ).left]
    [LocallyOfFinitePresentation (g ≫ δ).left] : P δ.left := by
  apply MorphismProperty.of_isPullback_of_descendsAlong
    (Q := @Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation)
    ((refinedKernelSquare δ H g).map (Over.forget _))
    ⟨⟨inferInstanceAs (Surjective (g ≫ δ).left),
      inferInstanceAs (Flat (g ≫ δ).left)⟩,
      inferInstanceAs (LocallyOfFinitePresentation (g ≫ δ).left)⟩
  exact P.of_isPullback ((IsPullback.of_hasPullback g p).map (Over.forget _)).flip hp

/-- Finite presentation is recovered before assuming it for the source projection. -/
theorem locallyOfFinitePresentation [LocallyOfFinitePresentation p.left]
    [Flat (g ≫ δ).left] [Surjective (g ≫ δ).left]
    [LocallyOfFinitePresentation (g ≫ δ).left] : LocallyOfFinitePresentation δ.left :=
  property δ H g _ inferInstance

/-- Smooth full relation endpoints give a smooth quotient projection. -/
theorem smooth [Smooth p.left] [Flat (g ≫ δ).left] [Surjective (g ≫ δ).left]
    [LocallyOfFinitePresentation (g ≫ δ).left] : Smooth δ.left :=
  property δ H g _ inferInstance

/-- Etale full relation endpoints give an etale quotient projection. -/
theorem etale [Etale p.left] [Flat (g ≫ δ).left] [Surjective (g ≫ δ).left]
    [LocallyOfFinitePresentation (g ≫ δ).left] : Etale δ.left :=
  property δ H g _ inferInstance

end FLT.Mazur.RelativeKernelPairPropertyDescent
