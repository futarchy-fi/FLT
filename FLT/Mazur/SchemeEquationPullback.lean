/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Full equation schemes on source charts

Restricting an equation to a source chart is a cartesian operation. In
particular an open source chart gives an open chart of the full equalizer.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.SchemeEquationPullback
variable {X Y T : Scheme.{0}} (f g : X ⟶ Y) (s : T ⟶ X)

/-- Restrict a full equation to an arbitrary source chart. -/
def map : equalizer (s ≫ f) (s ≫ g) ⟶ equalizer f g :=
  equalizer.lift (equalizer.ι (s ≫ f) (s ≫ g) ≫ s) (by
    simpa only [Category.assoc] using equalizer.condition (s ≫ f) (s ≫ g))

/-- The equation chart keeps its original source morphism. -/
@[reassoc] theorem map_ι :
    map f g s ≫ equalizer.ι f g = equalizer.ι (s ≫ f) (s ≫ g) ≫ s :=
  equalizer.lift_ι _ _

/-- The equation chart is the full pullback, including nilpotent coefficients. -/
theorem isPullback :
    IsPullback (map f g s) (equalizer.ι (s ≫ f) (s ≫ g)) (equalizer.ι f g) s := by
  apply IsPullback.of_isLimit' ⟨map_ι f g s⟩
  refine PullbackCone.IsLimit.mk _ (fun c ↦ equalizer.lift c.snd ?_) ?_ ?_ ?_
  · rw [← Category.assoc, ← c.condition, Category.assoc, equalizer.condition,
      ← Category.assoc, c.condition, Category.assoc]
  · intro c
    apply (cancel_mono (equalizer.ι f g)).mp
    rw [Category.assoc, map_ι, equalizer.lift_ι_assoc, c.condition]
  · intro c
    exact equalizer.lift_ι _ _
  · intro c m _ hm
    apply (cancel_mono (equalizer.ι (s ≫ f) (s ≫ g))).mp
    rw [hm, equalizer.lift_ι]

/-- Open source charts remain open on the exact equation scheme. -/
instance [IsOpenImmersion s] : IsOpenImmersion (map f g s) :=
  MorphismProperty.of_isPullback (isPullback f g s).flip inferInstance

/-- The image of an equation chart is precisely the inverse image of the source chart. -/
theorem range_map : Set.range (map f g s) = (equalizer.ι f g) ⁻¹' Set.range s := by
  rw [← (isPullback f g s).isoPullback_hom_fst]
  exact ((isPullback f g s).isoPullback.hom.surjective.range_comp _).trans
    (Scheme.Pullback.range_fst (equalizer.ι f g) s)

end FLT.Mazur.SchemeEquationPullback
