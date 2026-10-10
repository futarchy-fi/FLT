/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FinitelyPresentedLineSheafDescent

/-!
# Separated Noetherian models of finitely presented affine-base schemes

Using the structure module in line-sheaf descent gives a separated,
quasi-compact model without any additional sheaf data on the input.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open FLT.Mazur.FCurve

namespace FLT.Mazur.Approximation

universe u

/-- A separated finitely presented scheme has a separated finite integer model. -/
theorem exists_separated_finite_presentation_model {A : Type u} [CommRing A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    [IsSeparated f] [QuasiCompact f] [LocallyOfFinitePresentation f]
    (s : Set A) (hs : s.Finite) :
    ∃ S : Subalgebra ℤ A, Algebra.FiniteType ℤ S ∧ s ⊆ S ∧
      ∃ (Y : Scheme.{u}) (q : Y ⟶ Spec (.of S)) (a : X ⟶ Y),
        IsSeparated q ∧ QuasiCompact q ∧ LocallyOfFinitePresentation q ∧
        IsPullback a f q (Spec.map (CommRingCat.ofHom (algebraMap S A))) := by
  let _ : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let _ : X.IsSeparated := ⟨by
    simpa only [terminal.comp_from] using
      (inferInstance : IsSeparated (f ≫ terminal.from (Spec (.of A))))⟩
  obtain ⟨S, hS, hsS, Y, q, M, hsep, hqc, hfp, _, a, ha, _⟩ :=
    exists_finite_presentation_separated_line_sheaf_descent f (structureModule X)
      structureModule_locallyFreeRankOne s hs
  exact ⟨S, hS, hsS, Y, q, a, hsep, hqc, hfp, ha⟩

end FLT.Mazur.Approximation
