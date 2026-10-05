/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteIntersectionGluedSheafRecovery
public import FLT.Mazur.FiniteIntersectionScalarGluingOver
public import FLT.Mazur.FinitelyPresentedIntersectionCocycleModel
public import FLT.Mazur.AffineIntersectionFinitePresentation
public import FLT.Mazur.LineTrivializationCocycleRecovery
public import FLT.Mazur.AffineIntersectionSeparated

/-!
# Finitely presented separated descent with line-sheaf recovery

The constructed model is separated, quasi-compact, and locally finitely
presented. Its line sheaf recovers by actual pullback along the cartesian
recovery map. Universal closedness remains a separate descent obligation.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.Approximation

universe u

/-- Descend to a separated finite-presentation model with cartesian and line-sheaf recovery. -/
theorem exists_finite_presentation_separated_line_sheaf_descent {A : Type u} [CommRing A]
    {X : Scheme.{u}} [CompactSpace X] [X.IsSeparated]
    (p : X ⟶ Spec (.of A)) [LocallyOfFinitePresentation p]
    (L : X.Modules) (hL : FLT.Mazur.FCurve.LocallyFreeRankOne L)
    (s : Set A) (hs : s.Finite) :
    ∃ S : Subalgebra ℤ A, Algebra.FiniteType ℤ S ∧ s ⊆ S ∧
      ∃ (Y : Scheme.{u}) (q : Y ⟶ Spec (.of S)) (M : Y.Modules),
        IsSeparated q ∧ QuasiCompact q ∧ LocallyOfFinitePresentation q ∧
        FLT.Mazur.FCurve.LocallyFreeRankOne M ∧
        ∃ f : X ⟶ Y,
          IsPullback f p q (Spec.map (CommRingCat.ofHom (algebraMap S A))) ∧
          Nonempty ((Scheme.Modules.pullback f).obj M ≅ L) := by
  classical
  obtain ⟨ι, hι, U, hU, heU, hcover⟩ := hL.finite_affine_trivializing_cover
  let := hι
  let eU := fun i ↦ (heU i).some
  let g := FLT.Mazur.FCurve.lineTrivializationCocycle eU
  let hg := FLT.Mazur.FCurve.lineTrivializationCocycleIso eU hcover
  obtain ⟨S, hS, hsS, D, hfp, e, he, hopen, hp, hc, y, hy, hnat, hmul⟩ :=
    exists_finite_presentation_intersection_closed_cocycle_model U p hU g s hs
  let := hopen
  let := hfp
  let E := finiteIntersectionScalarGluingIso U p hU hcover D hp e he
  let f := E.inv ≫ affineIntersectionGluingProjection D hp
  refine ⟨S, hS, hsS, (affineIntersectionGlueData D hp).glued,
    affineIntersectionGluedToBase D hp, affineIntersectionGluedModelSheaf D hp y hnat hmul,
    affineIntersectionGluedToBase_isSeparated D hc hp,
    affineIntersectionGluedToBase_quasiCompact D hp,
    affineIntersectionGluedToBase_locallyOfFinitePresentation D hp,
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
