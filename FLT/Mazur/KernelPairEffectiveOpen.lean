/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.MonomorphismRelativeOpen
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-!
# Effective full relations over an intrinsic quotient-target open

The whole inverse image of the original relation is a kernel pair over the
constructed target open. Its projection retains any original fppf properties.
The construction does not assert coverage of the original quotient target.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.KernelPairEffectiveOpen
set_option backward.isDefEq.respectTransparency false
variable {D A T : Scheme.{u}} (p q : D ⟶ A) (w : A ⟶ T) (h : p ≫ w = q ≫ w)
local notation "m" => pullback.lift p q h
local notation "v" => pullback.fst w w ≫ w

/-- The constructed open retains the whole candidate kernel over each of its points. -/
def targetOpen : T.Opens := MonomorphismRelativeOpen.targetOpen m v

local notation "U" => targetOpen p q w h

/-- The entire source over the constructed quotient-target open. -/
def source : Scheme := pullback w (U).ι

/-- The entire original relation over that same target open. -/
def relation : Scheme := pullback (p ≫ w) (U).ι

/-- The actual base-changed quotient projection. -/
def projection : source p q w h ⟶ (U).toScheme := pullback.snd _ _

/-- The first original endpoint on the complete retained relation. -/
def fst : relation p q w h ⟶ source p q w h :=
  pullback.lift (pullback.fst _ _ ≫ p) (pullback.snd _ _)
    (by rw [Category.assoc]; exact pullback.condition)

/-- The independent second original endpoint on the same complete relation. -/
def snd : relation p q w h ⟶ source p q w h :=
  pullback.lift (pullback.fst _ _ ≫ q) (pullback.snd _ _)
    (by rw [Category.assoc, ← h]; exact pullback.condition)

@[reassoc]
theorem fst_original : fst p q w h ≫ pullback.fst w (U).ι =
    pullback.fst (p ≫ w) (U).ι ≫ p := pullback.lift_fst _ _ _

@[reassoc]
theorem snd_original : snd p q w h ≫ pullback.fst w (U).ι =
    pullback.fst (p ≫ w) (U).ι ≫ q := pullback.lift_fst _ _ _

/-- The whole retained relation is coequalized by the actual projection. -/
theorem condition : fst p q w h ≫ projection p q w h =
    snd p q w h ≫ projection p q w h := by
  simp only [fst, snd, projection, pullback.lift_snd]

instance projection_flat [Flat w] : Flat (projection p q w h) :=
  inferInstanceAs (Flat (pullback.snd _ _))

instance projection_surjective [Surjective w] : Surjective (projection p q w h) :=
  inferInstanceAs (Surjective (pullback.snd _ _))

instance projection_locallyOfFinitePresentation [LocallyOfFinitePresentation w] :
    LocallyOfFinitePresentation (projection p q w h) :=
  inferInstanceAs (LocallyOfFinitePresentation (pullback.snd _ _))

instance projection_quasiCompact [QuasiCompact w] : QuasiCompact (projection p q w h) :=
  inferInstanceAs (QuasiCompact (pullback.snd _ _))


variable [Mono (pullback.lift p q h)]

/-- Every pair over the retained quotient target has a unique original relation arrow. -/
theorem original_test_lift {Z : Scheme.{u}} (a b : Z ⟶ source p q w h)
    (hab : a ≫ projection p q w h = b ≫ projection p q w h) :
    ∃! z : Z ⟶ D,
      z ≫ p = a ≫ pullback.fst w (U).ι ∧ z ≫ q = b ≫ pullback.fst w (U).ι := by
  have he : (a ≫ pullback.fst w (U).ι) ≫ w = (b ≫ pullback.fst w (U).ι) ≫ w := by
    rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc,
      ← Category.assoc]
    exact congrArg (fun t ↦ t ≫ (U).ι) hab
  let k := pullback.lift (a ≫ pullback.fst w (U).ι) (b ≫ pullback.fst w (U).ι) he
  have hk : Set.range (k ≫ v) ⊆ U := by
    have e : k ≫ v = (a ≫ projection p q w h) ≫ (U).ι := by
      rw [← Category.assoc, pullback.lift_fst, Category.assoc, pullback.condition]
      rfl
    rw [e]
    rintro _ ⟨x, rfl⟩
    exact ((a ≫ projection p q w h) x).property
  obtain ⟨z, hz, hunique⟩ := MonomorphismRelativeOpen.test_lift m v k hk
  refine ⟨z, ⟨?_, ?_⟩, ?_⟩
  · have e := congrArg (fun t ↦ t ≫ pullback.fst w w) hz
    simpa only [Category.assoc, pullback.lift_fst, k] using e
  · have e := congrArg (fun t ↦ t ≫ pullback.snd w w) hz
    simpa only [Category.assoc, pullback.lift_snd, k] using e
  · intro z' hz'
    apply hunique z'
    apply pullback.hom_ext
    · simpa only [Category.assoc, pullback.lift_fst, k] using hz'.1
    · simpa only [Category.assoc, pullback.lift_snd, k] using hz'.2

/-- No effective-model premise is used: the complete restricted relation is a kernel pair. -/
theorem isPullback : IsPullback (fst p q w h) (snd p q w h)
    (projection p q w h) (projection p q w h) := by
  refine IsPullback.of_isLimit
    (PullbackCone.IsLimit.mk (condition p q w h) (fun c ↦ ?_) ?_ ?_ ?_)
  · let z := (original_test_lift p q w h c.fst c.snd c.condition).choose
    have hz := (original_test_lift p q w h c.fst c.snd c.condition).choose_spec.1
    exact pullback.lift z (c.fst ≫ projection p q w h) (by
      rw [← Category.assoc, hz.1, Category.assoc, pullback.condition]
      rfl)
  · intro c
    apply pullback.hom_ext
    · simp only [Category.assoc, fst_original, pullback.lift_fst_assoc]
      exact (original_test_lift p q w h c.fst c.snd c.condition).choose_spec.1.1
    · simp only [fst, projection, Category.assoc, pullback.lift_snd]
  · intro c
    apply pullback.hom_ext
    · simp only [Category.assoc, snd_original, pullback.lift_fst_assoc]
      exact (original_test_lift p q w h c.fst c.snd c.condition).choose_spec.1.2
    · simpa only [snd, projection, Category.assoc, pullback.lift_snd] using c.condition
  · intro c z hz₁ hz₂
    apply pullback.hom_ext
    · dsimp only
      rw [pullback.lift_fst]
      apply (original_test_lift p q w h c.fst c.snd c.condition).choose_spec.2
      constructor
      · simpa only [Category.assoc, fst_original] using
          congrArg (fun t ↦ t ≫ pullback.fst w (U).ι) hz₁
      · simpa only [Category.assoc, snd_original] using
          congrArg (fun t ↦ t ≫ pullback.fst w (U).ι) hz₂
    · simpa only [Category.assoc, fst, projection, pullback.lift_snd] using
        congrArg (fun t ↦ t ≫ projection p q w h) hz₁


end FLT.Mazur.KernelPairEffectiveOpen
