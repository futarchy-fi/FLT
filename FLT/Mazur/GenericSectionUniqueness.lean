/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.OverPoints
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Generic uniqueness of integral sections

Sections of a separated scheme over a reduced base are determined by their
restriction along any dominant morphism. This supplies the uniqueness part of
G1-D2 without assuming properness or a moduli interpretation.

Source: Stacks 01RH, as formalized by
`AlgebraicGeometry.ext_of_isDominant_of_isSeparated`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace FLT.Mazur

/-- Dominant restriction detects equality of sections of a separated scheme. -/
theorem Sections.restrict_injective_of_dominant {S T : Scheme.{u}} [IsReduced S]
    (X : Over S) [IsSeparated X.hom] (g : T ⟶ S) [IsDominant g] :
    Function.Injective (Sections.restrict (X := X) g) := by
  intro x y h
  apply Over.OverMorphism.ext
  exact ext_of_isDominant_of_isSeparated (X := S) X.hom
    ((Over.w x).trans (Over.w y).symm) g (congrArg (fun z => z.left) h)

/-- The same uniqueness statement for points over an arbitrary reduced affine source. -/
theorem Points.precomp_injective_of_dominant {S : Scheme.{u}} (X : Over S)
    [IsSeparated X.hom] {R K : Type u} [CommRing R] [CommRing K]
    [IsReduced (Spec (CommRingCat.of R))]
    (s : Spec (CommRingCat.of R) ⟶ S)
    (g : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R)) [IsDominant g] :
    Function.Injective (Points.precomp (X := X) (s := s) g) := by
  intro x y h
  apply Over.OverMorphism.ext
  exact ext_of_isDominant_of_isSeparated (X := Spec (CommRingCat.of R)) X.hom
    ((Over.w x).trans (Over.w y).symm) g (congrArg (fun z => z.left) h)

end FLT.Mazur
