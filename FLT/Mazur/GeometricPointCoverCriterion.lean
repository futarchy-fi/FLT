/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Geometric tests detect covering families

A family of scheme maps covers if every algebraically closed field-valued
point factors through one member. Algebraic closures of the actual residue
fields supply the required geometric points.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.GeometricPointCoverCriterion

universe u v
variable {I : Type v} {X : Scheme.{u}} {Y : I → Scheme.{u}} (f : ∀ i, Y i ⟶ X)

/-- Factorization on geometric tests gives coverage of the entire underlying space. -/
theorem covers
    (h : ∀ (K : Type u) [Field K] [IsAlgClosed K] (p : Spec (.of K) ⟶ X),
      ∃ (i : I) (q : Spec (.of K) ⟶ Y i), q ≫ f i = p) (x : X) :
    ∃ (i : I) (y : Y i), f i y = x := by
  let K := AlgebraicClosure (X.residueField x)
  let g : Spec (.of K) ⟶ Spec (X.residueField x) :=
    Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) K))
  obtain ⟨i, q, hq⟩ := h K (g ≫ X.fromSpecResidueField x)
  refine ⟨i, q (IsLocalRing.closedPoint K), ?_⟩
  calc
    _ = (q ≫ f i) (IsLocalRing.closedPoint K) := rfl
    _ = (g ≫ X.fromSpecResidueField x) (IsLocalRing.closedPoint K) :=
      congrArg (fun k : Spec (.of K) ⟶ X ↦ k (IsLocalRing.closedPoint K)) hq
    _ = x := X.fromSpecResidueField_apply x _

end FLT.Mazur.GeometricPointCoverCriterion
