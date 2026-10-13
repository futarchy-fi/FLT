/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteSmoothRotation
public import FLT.Mazur.ConstantCyclicSchemeAction

/-!
# Actual constant cyclic actions on the complete family and its smooth open

Coproduct descent assembles the original rotations on every cartesian square.
Both action morphisms satisfy the unit and associativity laws, and the actual
smooth inclusion intertwines them on the whole group scheme.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase completeRotation
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  {S Y : Scheme} (s : S ⟶ Spec (.of (PowerSeries K)))
  (p : Y ⟶ exactVeroneseProj K n h) (q : Y ⟶ S)
  (hs : IsPullback p q (exactVeroneseProjToBase K n h) s)

/-- The actual original rotation as a morphism over the specified base. -/
def completeCartesianRotationOver (a : ZMod n) : Over.mk q ⟶ Over.mk q :=
  Over.homMk (completeCartesianRotation K n h s p q hs a)
    (completeCartesianRotation_snd K n h s p q hs a)

/-- The constant cyclic group acts on the actual whole complete-family square. -/
def completeCyclicAction : ConstantCyclicGroup.model S n ⊗ Over.mk q ⟶ Over.mk q :=
  ConstantCyclicSchemeAction.act (completeCartesianRotationOver K n h s p q hs)

/-- The whole-family action has the actual unit law. -/
theorem completeCyclicAction_unit :
    η[ConstantCyclicGroup.model S n] ▷ Over.mk q ≫ completeCyclicAction K n h s p q hs =
      (λ_ (Over.mk q)).hom := by
  apply ConstantCyclicSchemeAction.unit_act
  apply Over.OverMorphism.ext
  exact completeCartesianRotation_zero K n h s p q hs

/-- The whole-family action has the actual associativity law. -/
theorem completeCyclicAction_assoc :
    μ[ConstantCyclicGroup.model S n] ▷ Over.mk q ≫ completeCyclicAction K n h s p q hs =
      (α_ (ConstantCyclicGroup.model S n) (ConstantCyclicGroup.model S n) (Over.mk q)).hom ≫
        ConstantCyclicGroup.model S n ◁ completeCyclicAction K n h s p q hs ≫
          completeCyclicAction K n h s p q hs := by
  apply ConstantCyclicSchemeAction.assoc_act
  intro a b
  apply Over.OverMorphism.ext
  exact completeCartesianRotation_add K n h s p q hs a b

variable [LocallyOfFinitePresentation q]

/-- The actual restricted smooth rotation over the original base. -/
def completeSmoothCartesianRotationOver (a : ZMod n) :
    Over.mk (q.smoothLocus.ι ≫ q) ⟶ Over.mk (q.smoothLocus.ι ≫ q) :=
  Over.homMk (completeSmoothCartesianRotation K n h s p q hs a)
    (completeSmoothCartesianRotation_toBase K n h s p q hs a)

/-- The full constant cyclic group scheme acts on the actual smooth open. -/
def completeSmoothCyclicAction :
    ConstantCyclicGroup.model S n ⊗ Over.mk (q.smoothLocus.ι ≫ q) ⟶
      Over.mk (q.smoothLocus.ι ≫ q) :=
  ConstantCyclicSchemeAction.act (completeSmoothCartesianRotationOver K n h s p q hs)

/-- The smooth action has the unit law. -/
theorem completeSmoothCyclicAction_unit :
    η[ConstantCyclicGroup.model S n] ▷ Over.mk (q.smoothLocus.ι ≫ q) ≫
      completeSmoothCyclicAction K n h s p q hs = (λ_ (Over.mk (q.smoothLocus.ι ≫ q))).hom := by
  apply ConstantCyclicSchemeAction.unit_act
  apply Over.OverMorphism.ext
  exact completeSmoothCartesianRotation_zero K n h s p q hs

/-- The smooth action has the associativity law. -/
theorem completeSmoothCyclicAction_assoc :
    μ[ConstantCyclicGroup.model S n] ▷ Over.mk (q.smoothLocus.ι ≫ q) ≫
      completeSmoothCyclicAction K n h s p q hs =
        (α_ (ConstantCyclicGroup.model S n) (ConstantCyclicGroup.model S n)
          (Over.mk (q.smoothLocus.ι ≫ q))).hom ≫
            ConstantCyclicGroup.model S n ◁ completeSmoothCyclicAction K n h s p q hs ≫
              completeSmoothCyclicAction K n h s p q hs := by
  apply ConstantCyclicSchemeAction.assoc_act
  intro a b
  apply Over.OverMorphism.ext
  exact completeSmoothCartesianRotation_add K n h s p q hs a b

/-- The actual smooth inclusion intertwines the entire group scheme actions. -/
theorem completeSmoothCyclicAction_inclusion :
    completeSmoothCyclicAction K n h s p q hs ≫
      (Over.homMk q.smoothLocus.ι rfl : Over.mk (q.smoothLocus.ι ≫ q) ⟶ Over.mk q) =
        ConstantCyclicGroup.model S n ◁ Over.homMk q.smoothLocus.ι rfl ≫
          completeCyclicAction K n h s p q hs := by
  apply FiniteCoproductTensorRight.hom_ext (fun _ : ZMod n ↦ 𝟙_ (Over S))
  intro a
  rw [show Sigma.ι (fun _ : ZMod n ↦ 𝟙_ (Over S)) a =
      ConstantCyclicGroup.component S n a from rfl]
  change _ ≫ ConstantCyclicSchemeAction.act _ ≫ _ =
    _ ≫ _ ◁ _ ≫ ConstantCyclicSchemeAction.act _
  rw [ConstantCyclicSchemeAction.component_act_assoc, ← tensorHom_def_assoc,
    tensorHom_def'_assoc, ConstantCyclicSchemeAction.component_act,
    leftUnitor_naturality_assoc]
  congr 1
  apply Over.OverMorphism.ext
  exact completeSmoothCartesianRotation_ι K n h s p q hs a

end FLT.Mazur.PolygonInfinitesimalStages
