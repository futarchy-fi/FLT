/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic

/-!
# Algebraically closed sections detect maps to a relatively separated target

The target need not be a scheme over the algebraically closed field.
This permits equality tests for maps to the original rational target of descent.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace FLT.Mazur.AlgClosedSectionHomExt

universe u
variable {K : Type u} [Field K] [IsAlgClosed K] {X Y Z : Scheme.{u}}
  (s : X ⟶ Spec (.of K)) [LocallyOfFiniteType s] [IsReduced X]
  (i : Y ⟶ Z) [IsSeparated i]

/-- Sections over the closed field detect relatively separated maps even to another base. -/
theorem hom_ext (f g : X ⟶ Y) (hbase : f ≫ i = g ≫ i)
    (h : ∀ p : Spec (.of K) ⟶ X, p ≫ s = 𝟙 _ → p ≫ f = p ≫ g) : f = g := by
  let _ : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace s
  apply ext_of_fromSpecResidueField_eq f g i (closedPoints X) _ _ hbase
  · rw [dense_iff_closure_eq]
    simpa only [Set.univ_inter, closure_univ] using
      (JacobsonSpace.closure_inter_closedPoints_eq_closure
        (S := Set.univ) isOpen_univ.isLocallyClosed)
  · intro x hx
    apply (cancel_epi (Spec.map (residueFieldIsoBase s x hx).hom)).mp
    exact h (pointOfClosedPoint s x hx) (pointOfClosedPoint_comp s x hx)

end FLT.Mazur.AlgClosedSectionHomExt
