/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteIntersectionGluedSheafRecovery
public import FLT.Mazur.FiniteIntersectionScalarGluingOver
public import FLT.Mazur.FiniteLineCocycleModel

/-!
# Finite coefficient descent of a scheme with a line sheaf

For a compact separated scheme locally of finite presentation over an affine
base, a line sheaf descends together with the scheme to a finite integer
coefficient algebra. Recovery includes an isomorphism with the actual sheaf
pullback along the same cartesian scheme-recovery morphism.

This does not descend properness or ampleness, and does not remove the local
finite-presentation hypothesis from the proper-only approximation target.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.Approximation

universe u

/-- A line sheaf and its scheme descend to finite integer coefficients with actual recovery. -/
theorem exists_finite_line_sheaf_descent {A : Type u} [CommRing A]
    {X : Scheme.{u}} [CompactSpace X] [X.IsSeparated]
    (p : X ⟶ Spec (.of A)) [LocallyOfFinitePresentation p]
    (L : X.Modules) (hL : FLT.Mazur.FCurve.LocallyFreeRankOne L)
    (s : Set A) (hs : s.Finite) :
    ∃ S : Subalgebra ℤ A, Algebra.FiniteType ℤ S ∧ s ⊆ S ∧
      ∃ (Y : Scheme.{u}) (q : Y ⟶ Spec (.of S)) (M : Y.Modules),
        FLT.Mazur.FCurve.LocallyFreeRankOne M ∧
        ∃ f : X ⟶ Y,
          IsPullback f p q (Spec.map (CommRingCat.ofHom (algebraMap S A))) ∧
          Nonempty ((Scheme.Modules.pullback f).obj M ≅ L) := by
  obtain ⟨ι, hι, U, hU, hcover, g, ⟨hg⟩, S, hS, hsS, D, e, he,
    hopen, hp, y, hy, hnat, hmul⟩ := exists_finite_line_cocycle_model p L hL s hs
  let := hι
  let := hopen
  let E := finiteIntersectionScalarGluingIso U p hU hcover D hp e he
  let f := E.inv ≫ affineIntersectionGluingProjection D hp
  refine ⟨S, hS, hsS, (affineIntersectionGlueData D hp).glued,
    affineIntersectionGluedToBase D hp, affineIntersectionGluedModelSheaf D hp y hnat hmul,
    affineIntersectionGluedModelSheaf_rankOne D hp y hnat hmul, f, ?_, ?_⟩
  · apply (affineIntersectionGluing_isPullback (A := A) D hp).of_iso
      E (Iso.refl _) (Iso.refl _) (Iso.refl _)
    · simp [f]
    · simpa [E] using (finiteIntersectionScalarGluingIso_over U p hU hcover D hp e he).symm
    · simp
    · simp
  · exact ⟨finiteIntersectionGluedModelSheafRecoveryIso
      U p hU hcover D hp e he g y hnat hmul hy ≪≫ hg⟩

end FLT.Mazur.Approximation
