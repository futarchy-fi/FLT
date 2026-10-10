/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeometricPointCoverCriterion

/-!
# Geometric tests detect units of global sections

Invertibility can be tested on algebraically closed field-valued points.
This criterion holds on nonreduced schemes as well.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.GeometricSectionUnits

universe u
variable (X : Scheme.{u}) (r : Γ(X, ⊤))

/-- A section whose pullback to every geometric point is a unit is itself a unit. -/
theorem isUnit_of_geometric
    (h : ∀ (K : Type u) [Field K] [IsAlgClosed K] (p : Spec (.of K) ⟶ X),
      IsUnit (p.appTop r)) : IsUnit r := by
  apply X.toLocallyRingedSpace.toRingedSpace.isUnit_of_isUnit_germ
  intro x hx
  apply (X.mem_basicOpen_top r x).mp
  let K := AlgebraicClosure (X.residueField x)
  let g : Spec (.of K) ⟶ Spec (X.residueField x) :=
    Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) K))
  let p := g ≫ X.fromSpecResidueField x
  have hp : p (IsLocalRing.closedPoint K) ∈ X.basicOpen r := by
    change IsLocalRing.closedPoint K ∈ p ⁻¹ᵁ X.basicOpen r
    rw [Scheme.preimage_basicOpen_top, Scheme.basicOpen_of_isUnit _ (h K p)]
    trivial
  have he : p (IsLocalRing.closedPoint K) = x := X.fromSpecResidueField_apply x _
  rwa [he] at hp

end FLT.Mazur.GeometricSectionUnits
