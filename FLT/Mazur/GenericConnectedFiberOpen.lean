/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineResidueEvaluationComparison
public import FLT.Mazur.IncreasingCechFiberEvaluation

/-!
# Actual connected fibers form an open set on a nonempty generic open

The generic comparison of actual functions and tensor functions identifies
the connected fibers there with the open finite-module evaluation locus.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.Approximation
open ArtinianRelativeSectionCriterion IncreasingCechCartesian

variable {R : CommRingCat.{0}} [IsNoetherianRing R] [IsDomain R]
  {X : Scheme.{0}} (f : X ⟶ Spec R) [IsProper f] [Smooth f] [X.IsSeparated]
  {ι : Type} [LinearOrder ι] [Finite ι] (U : ι → X.Opens)
  (hU : ∀ i, IsAffineOpen (U i)) (hCover : iSup U = ⊤)
  (s : Spec R ⟶ X) (hs : s ≫ f = 𝟙 _)

include hU hCover s hs in
/-- On one nonzero original-ring principal open, the actual connected-fiber locus is open. -/
theorem exists_generic_isOpen_connectedFiber_inter :
    ∃ r : R, r ≠ 0 ∧ IsOpen
      (geometricallyConnectedLocus f ∩ (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R))) := by
  let e := affineSectionRingEquiv R
  let _ : IsNoetherianRing Γ(Spec R, ⊤) := isNoetherianRing_of_ringEquiv R e.symm
  let _ : IsDomain Γ(Spec R, ⊤) := e.toMulEquiv.isDomain R
  obtain ⟨r, hr, he⟩ := exists_generic_connectedFiber_iff_tensor f U hU hCover s hs
  let E : Set (Spec R) := {b |
    let _ : Algebra Γ(Spec R, ⊤) Γ(Spec ((Spec R).residueField b), ⊤) :=
      ((Spec R).fromSpecResidueField b).appTop.hom.toAlgebra
    Function.Injective ((evaluation f s hs).lTensor Γ(Spec ((Spec R).residueField b), ⊤))}
  have hE : IsOpen E := isOpen_actualResidueTensorEvaluationLocus f s hs
  have hEq : geometricallyConnectedLocus f ∩ ((Spec R).basicOpen r : Set (Spec R)) =
      E ∩ ((Spec R).basicOpen r : Set (Spec R)) := by
    ext b
    constructor
    · rintro ⟨hb, hbr⟩
      exact ⟨(he b hbr).mp hb, hbr⟩
    · rintro ⟨hb, hbr⟩
      exact ⟨(he b hbr).mpr hb, hbr⟩
  refine ⟨e r, fun hz ↦ hr (e.injective (hz.trans (map_zero e).symm)), ?_⟩
  have hopen : IsOpen
      (geometricallyConnectedLocus f ∩ ((Spec R).basicOpen r : Set (Spec R))) := by
    rw [hEq]
    exact hE.inter ((Spec R).basicOpen r).isOpen
  rw [AlgebraicGeometry.basicOpen_eq_of_affine'] at hopen
  exact hopen

end FLT.Mazur.Approximation
