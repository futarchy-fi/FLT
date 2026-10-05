/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteIntersectionSchemeDescent

/-!
# Integer models of compact separated locally finitely presented schemes

Compactness supplies the finite affine atlas required by intersection
scheme descent. The result recovers the entire scheme by base change;
it does not assert descent of properness or an invertible sheaf.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.Approximation

universe u

/-- A compact separated scheme locally finitely presented over an affine base
has a scheme model over a finite-type integer subalgebra. -/
theorem exists_compact_scheme_integer_model {A : Type u} [CommRing A]
    {X : Scheme.{u}} [CompactSpace X] [X.IsSeparated]
    (p : X ⟶ Spec (.of A)) [LocallyOfFinitePresentation p]
    (s : Set A) (hs : s.Finite) :
    ∃ S : Subalgebra ℤ A, Algebra.FiniteType ℤ S ∧ s ⊆ S ∧
      ∃ (Y : Scheme.{u}) (q : Y ⟶ Spec (.of S)) (f : X ⟶ Y),
        IsPullback f p q (Spec.map (CommRingCat.ofHom (algebraMap S A))) := by
  obtain ⟨t, ht, htop⟩ :=
    (isCompact_iff_finite_and_eq_biUnion_affineOpens (X := X) (U := ⊤)).mp isCompact_univ
  let := ht.to_subtype
  apply exists_finite_intersection_scheme_model (fun i : t ↦ i.val.val) p
    (fun i ↦ i.val.property) _ s hs
  simpa only [iSup_subtype] using htop.symm

end FLT.Mazur.Approximation
