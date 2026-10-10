/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeometricPointCoverCriterion
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-!
# Geometric points detect factorization through an open immersion

Factoring every algebraically closed field test through an open forces an
actual scheme factorization. The source need not be reduced.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.GeometricOpenFactorization

universe u
variable {U X Y : Scheme.{u}} (i : U ⟶ X) [IsOpenImmersion i] (f : Y ⟶ X)
  (h : ∀ (K : Type u) [Field K] [IsAlgClosed K] (p : Spec (.of K) ⟶ Y),
    ∃ q : Spec (.of K) ⟶ U, q ≫ i = p ≫ f)

include h

omit [IsOpenImmersion i] in
/-- The image condition for an open immersion can be checked on geometric points. -/
theorem range_subset : Set.range f ⊆ Set.range i := by
  rintro _ ⟨y, rfl⟩
  let K := AlgebraicClosure (Y.residueField y)
  let g : Spec (.of K) ⟶ Spec (Y.residueField y) :=
    Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) K))
  obtain ⟨q, hq⟩ := h K (g ≫ Y.fromSpecResidueField y)
  refine ⟨q (IsLocalRing.closedPoint K), ?_⟩
  calc
    _ = (q ≫ i) (IsLocalRing.closedPoint K) := rfl
    _ = ((g ≫ Y.fromSpecResidueField y) ≫ f) (IsLocalRing.closedPoint K) :=
      congrArg (fun k : Spec (.of K) ⟶ X ↦ k (IsLocalRing.closedPoint K)) hq
    _ = f y := congrArg f (Y.fromSpecResidueField_apply y _)

/-- The actual lift retains all infinitesimal information in the source. -/
def lift : Y ⟶ U := IsOpenImmersion.lift i f (range_subset i f h)

/-- The geometric lifting criterion yields equality of the original scheme morphisms. -/
@[reassoc (attr := simp)] theorem lift_fac : lift i f h ≫ i = f :=
  IsOpenImmersion.lift_fac i f _

end FLT.Mazur.GeometricOpenFactorization
