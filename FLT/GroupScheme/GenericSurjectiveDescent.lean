/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudFlatQuotient

/-! # Descent of an equivariant generic morphism through a surjection -/

@[expose] public noncomputable section
namespace ThreeAdicPlan.GenericGaloisHom
variable {R K : Type} [CommRing R] [Field K] [Algebra R K] {X Y Z : FF R K}

/-- Descend an actual equivariant morphism when it kills the kernel of a surjection. -/
def descendThroughSurjective (q : GenericGaloisHom X Y) (hq : Function.Surjective q)
    (g : GenericGaloisHom X Z) (hk : q.toAddMonoidHom.ker ≤ g.toAddMonoidHom.ker) :
    GenericGaloisHom Y Z := by
  let h := q.toAddMonoidHom.liftOfSurjective hq ⟨g.toAddMonoidHom, hk⟩
  have hh (x : X.Points) : h (q x) = g x :=
    AddMonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _
  refine { h with map_smul' := ?_ }
  intro σ y
  obtain ⟨x, rfl⟩ := hq y
  change h (σ • q x) = σ • h (q x)
  calc
    h (σ • q x) = h (q (σ • x)) := congrArg h (map_smul q σ x).symm
    _ = g (σ • x) := hh _
    _ = σ • g x := map_smul g σ x
    _ = σ • h (q x) := congrArg (σ • ·) (hh x).symm

/-- The descended map recovers the specified morphism on every original point. -/
theorem descendThroughSurjective_apply (q : GenericGaloisHom X Y)
    (hq : Function.Surjective q) (g : GenericGaloisHom X Z)
    (hk : q.toAddMonoidHom.ker ≤ g.toAddMonoidHom.ker) (x : X.Points) :
    q.descendThroughSurjective hq g hk (q x) = g x := by
  change (q.toAddMonoidHom.liftOfSurjective hq ⟨g.toAddMonoidHom, hk⟩) (q x) = g x
  exact AddMonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _
end ThreeAdicPlan.GenericGaloisHom
