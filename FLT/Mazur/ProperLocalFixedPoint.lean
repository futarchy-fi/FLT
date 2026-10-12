/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Fiber

/-!
# A proper fixed-point scheme over a local base

The scheme equalizer is proper over the base. Any of its points specializes
to the closed fiber, so absence of closed-fiber fixed points makes it empty.
This concerns scheme-theoretic fixed points, not invariant underlying prime ideals.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.ProperLocalFixedPoint
universe u
variable (R : Type u) [CommRing R] [IsLocalRing R]
  {X : Over (Spec (.of R))} [IsProper X.hom] (f : X ⟶ X)
  (hf : ∀ x : X.left, X.hom x = IsLocalRing.closedPoint R → f.left x ≠ x)

include hf in
/-- A fixed-point equalizer with empty closed fiber has no points over a local proper base. -/
theorem equalizer_isEmpty : IsEmpty (equalizer f (𝟙 X)).left := by
  let E := equalizer f (𝟙 X)
  let j : E ⟶ X := equalizer.ι f (𝟙 X)
  have hj : j.left ≫ X.hom = E.hom := j.w
  let _ : IsProper E.hom := by
    rw [← hj]
    infer_instance
  refine ⟨fun z ↦ ?_⟩
  obtain ⟨w, _, hw⟩ := E.hom.isClosedMap.specializingMap
    (a := z) (IsLocalRing.specializes_closedPoint (E.hom z))
  have hb : X.hom (j.left w) = IsLocalRing.closedPoint R :=
    (congrArg (fun g ↦ g w) hj).trans hw
  apply hf (j.left w) hb
  have he := congrArg (fun g : E ⟶ X ↦ g.left w) (equalizer.condition f (𝟙 X))
  exact he

include hf in
/-- No nonempty test scheme can carry an invariant morphism into the proper family. -/
theorem comp_ne {T : Over (Spec (.of R))} [Nonempty T.left] (p : T ⟶ X) :
    p ≫ f ≠ p := by
  intro he
  let _ := equalizer_isEmpty R f hf
  let q : T ⟶ equalizer f (𝟙 X) := equalizer.lift p (by simpa using he)
  obtain ⟨t⟩ := ‹Nonempty T.left›
  exact isEmptyElim (q.left t)

end FLT.Mazur.ProperLocalFixedPoint
