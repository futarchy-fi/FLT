/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.ProjectiveSpaceCharts
public import FLT.Mazur.CoherentSubquotient
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
public import Mathlib.RingTheory.GradedAlgebra.Noetherian

/-! # Noetherian projective charts and coherent kernels -/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial

universe u

namespace FLT.Mazur.ProjectiveSpace

variable (R : Type u) [CommRing R] (ι : Type u) [Finite ι]

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Finite coordinates generate the polynomial ring over its degree-zero subring. -/
instance coordinateAlgebra_finiteType :
    Algebra.FiniteType (grading R ι 0) (MvPolynomial ι R) := by
  classical
  let _index : Fintype ι := Fintype.ofFinite ι
  refine ⟨⟨Finset.univ.image X, ?_⟩⟩
  simpa using adjoin_coordinates R ι

variable [IsNoetherianRing R]

/-- Every standard homogeneous-localization chart ring is Noetherian. -/
instance chartRing_isNoetherian (i : ι) : IsNoetherianRing (chartRing R ι i) := by
  let _finiteType := HomogeneousLocalization.Away.finiteType
    (𝒜 := grading R ι) (X i) 1 (isHomogeneous_X R i)
  exact Algebra.FiniteType.isNoetherianRing (grading R ι 0) (chartRing R ι i)

/-- Polynomial projective space over a Noetherian base is locally Noetherian. -/
instance space_isLocallyNoetherian : IsLocallyNoetherian (space R ι) :=
  LocallyOfFiniteType.isLocallyNoetherian (Proj.toSpecZero (grading R ι))

/-- Kernels of maps between coherent projective sheaves are coherent. -/
theorem projective_coherent_kernel {M N : (space R ι).Modules}
    [M.IsFinitePresentation] [N.IsFinitePresentation] (f : M ⟶ N) :
    (kernel f).IsFinitePresentation :=
  FCurve.CoherentDevissage.coherent_kernel f

end FLT.Mazur.ProjectiveSpace
