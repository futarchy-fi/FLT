/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LocallyRingedOpenImage

/-!
# Cartesian squares from exact locally ringed open images

A commuting square with an open immersion on the source side and a monomorphism
on the target side is cartesian when the source image is exactly the inverse
image of the target image. The proof uses the actual open-immersion lift.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.LocallyRingedOpenImage
variable {X Y Z T : LocallyRingedSpace.{u}}
  (f : X ⟶ Y) (i : X ⟶ Z) (j : Y ⟶ T) (g : Z ⟶ T)
  [LocallyRingedSpace.IsOpenImmersion i] [Mono j]

/-- An exact open inverse-image square is a pullback of locally ringed spaces. -/
theorem isPullback_of_range (h : f ≫ j = i ≫ g)
    (hr : Set.range i.base = g.base ⁻¹' Set.range j.base) : IsPullback f i j g := by
  have hS (s : PullbackCone j g) : Set.range s.snd.base ⊆ Set.range i.base := by
    rw [hr]
    rintro _ ⟨x, rfl⟩
    refine ⟨s.fst.base x, ?_⟩
    exact congrArg (fun k => k.base x) s.condition
  let l (s : PullbackCone j g) := LocallyRingedSpace.IsOpenImmersion.lift i s.snd (hS s)
  have hl (s : PullbackCone j g) : l s ≫ i = s.snd :=
    LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ _
  apply IsPullback.of_isLimit (PullbackCone.IsLimit.mk h l ?_ hl ?_)
  · intro s
    rw [← cancel_mono j, Category.assoc, h, ← Category.assoc, hl]
    exact s.condition.symm
  · intro s m _ hm
    rw [← cancel_mono i, hm, hl]

end FLT.Mazur.LocallyRingedOpenImage
