/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OrderedCurvePowerSuccessor
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Smoothness of the fixed ordered parameter schemes

The actual wide-pullback powers are smooth over the original base, including
the empty power. The proof uses the cartesian successor decomposition.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace FLT.Mazur.OrderedCurvePower
variable {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f]

/-- Forgetting one ordered point is a smooth morphism. -/
theorem tail_smooth (n : ℕ) : Smooth (tail f n) :=
  MorphismProperty.of_isPullback (successor_isPullback f n) inferInstance

/-- Every fixed ordered power has a smooth structural map to the unchanged base. -/
theorem base_smooth (n : ℕ) : Smooth (base f n) := by
  induction n with
  | zero => exact inferInstanceAs (Smooth (emptyIso f).hom)
  | succ n hn =>
    let _ := hn
    let _ := tail_smooth f n
    rw [← tail_base f n]
    infer_instance

/-- Every ordered parameter base is flat over the original base. -/
theorem base_flat (n : ℕ) : Flat (base f n) := by
  let _ := base_smooth f n
  infer_instance

/-- Every ordered parameter base is locally of finite presentation. -/
theorem base_locallyOfFinitePresentation (n : ℕ) :
    LocallyOfFinitePresentation (base f n) := by
  let _ := base_smooth f n
  infer_instance

end FLT.Mazur.OrderedCurvePower
