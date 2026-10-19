/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeNilpotentSectionDetection
public import FLT.Mazur.GeometricPointCoverCriterion

/-!
# Geometric tests detect nilpotence of actual regular functions

Algebraic closures of residue fields test every point of a scheme. On a
quasi-compact scheme, a function vanishing on all such tests has a uniform
nilpotence exponent. No reducedness assumption is needed.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.SchemeGeometricNilpotentSections
universe u
variable {X : Scheme.{u}} [CompactSpace X]

/-- Vanishing on all algebraically closed field tests forces global nilpotence. -/
theorem isNilpotent_of_geometric_pullback (s : Γ(X, ⊤))
    (h : ∀ (K : Type u) [Field K] [IsAlgClosed K] (p : Spec (.of K) ⟶ X),
      p.appTop s = 0) : IsNilpotent s := by
  apply (Scheme.isNilpotent_iff_basicOpen_eq_bot s).mpr
  apply eq_bot_iff.mpr
  intro x hx
  let K := AlgebraicClosure (X.residueField x)
  let p : Spec (.of K) ⟶ X :=
    Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) K)) ≫
      X.fromSpecResidueField x
  have hp : p (IsLocalRing.closedPoint K) = x := X.fromSpecResidueField_apply x _
  have hy : IsLocalRing.closedPoint K ∈ p ⁻¹ᵁ X.basicOpen s := by
    change p (IsLocalRing.closedPoint K) ∈ X.basicOpen s
    rwa [hp]
  rw [Scheme.preimage_basicOpen_top, h K p, Scheme.basicOpen_zero] at hy
  exact hy

/-- Equality on geometric tests controls the entire discrepancy modulo nilpotents. -/
theorem isNilpotent_sub_of_geometric_pullback (s t : Γ(X, ⊤))
    (h : ∀ (K : Type u) [Field K] [IsAlgClosed K] (p : Spec (.of K) ⟶ X),
      p.appTop s = p.appTop t) : IsNilpotent (s - t) := by
  apply isNilpotent_of_geometric_pullback
  intro K _ _ p
  rw [map_sub, h K p, sub_self]

/-- Every geometric comparison has a finite, global power annihilating its discrepancy. -/
theorem exists_pow_sub_eq_zero_of_geometric_pullback (s t : Γ(X, ⊤))
    (h : ∀ (K : Type u) [Field K] [IsAlgClosed K] (p : Spec (.of K) ⟶ X),
      p.appTop s = p.appTop t) : ∃ k : ℕ, (s - t) ^ k = 0 :=
  isNilpotent_sub_of_geometric_pullback s t h

end FLT.Mazur.SchemeGeometricNilpotentSections
