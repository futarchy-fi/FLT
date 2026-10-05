/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteIntersectionScalarGluingOver
public import FLT.Mazur.FiniteIntersectionModelGluing

/-!
# Scheme descent from a finite affine intersection atlas

The descended affine diagram now gives a scheme model with a global
cartesian recovery square. Local finite presentation is used only for
this intermediate approximation result; the proper-only target still
requires further approximation and descent of sheaves and properness.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.Approximation

universe u v

/-- A finite affine atlas descends to a finite-type integer base with global recovery. -/
theorem exists_finite_intersection_scheme_model {A : Type u} [CommRing A]
    {X : Scheme.{u}} {ι : Type v} [Finite ι] (U : ι → X.Opens)
    (p : X ⟶ Spec (.of A)) [X.IsSeparated] [LocallyOfFinitePresentation p]
    (hU : ∀ i, IsAffineOpen (U i)) (hcover : iSup U = ⊤)
    (s : Set A) (hs : s.Finite) :
    ∃ S : Subalgebra ℤ A, Algebra.FiniteType ℤ S ∧ s ⊆ S ∧
      ∃ (Y : Scheme.{u}) (q : Y ⟶ Spec (.of S)) (f : X ⟶ Y),
        IsPullback f p q (Spec.map (CommRingCat.ofHom (algebraMap S A))) := by
  obtain ⟨S, hS, hsS, D, e, he, hopen, hp, _⟩ :=
    exists_finite_intersection_glued_model U p hU s hs
  let := hopen
  let E := finiteIntersectionScalarGluingIso U p hU hcover D hp e he
  refine ⟨S, hS, hsS, (affineIntersectionGlueData D hp).glued,
    affineIntersectionGluedToBase D hp, E.inv ≫ affineIntersectionGluingProjection D hp, ?_⟩
  apply (affineIntersectionGluing_isPullback (A := A) D hp).of_iso
    E (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simp
  · simpa [E] using (finiteIntersectionScalarGluingIso_over U p hU hcover D hp e he).symm
  · simp
  · simp

end FLT.Mazur.Approximation
