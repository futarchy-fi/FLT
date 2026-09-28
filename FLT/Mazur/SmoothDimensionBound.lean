/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EtaleCoordinate
public import FLT.Mazur.EtaleDimLe
public import FLT.Mazur.SmoothDimension

/-!
# Upper dimension bound for smooth curves

A standard-smooth presentation in relative dimension one is étale over a
polynomial ring in its free coordinate. The resulting upper dimension bound
glues over affine charts, including for an empty scheme.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace FLT.Mazur.FCurve

/-- A standard-smooth algebra of relative dimension one over a field has dimension at most one. -/
theorem ringKrullDim_le_one_of_standardSmooth
    {K A : Type u} [Field K] [CommRing A] (g : K →+* A)
    (hg : RingHom.IsStandardSmoothOfRelativeDimension 1 g) : ringKrullDim A ≤ 1 := by
  let := g.toAlgebra
  have : Algebra.IsStandardSmoothOfRelativeDimension 1 K A := hg
  obtain ⟨ι, σ, _, _, P, hP⟩ :=
    (inferInstance : Algebra.IsStandardSmoothOfRelativeDimension 1 K A).out
  let := (P.coordinateHom hP).toAlgebra
  have : Algebra.Etale (Polynomial K) A := P.coordinateHom_etale hP
  exact ringKrullDim_le_one_of_etale_polynomial K A

/-- A smooth scheme of relative dimension one over a field has dimension at most one. -/
theorem topologicalKrullDim_le_one_of_smooth
    {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of K)) [SmoothOfRelativeDimension 1 f] :
    topologicalKrullDim X ≤ 1 := by
  apply topologicalKrullDim_le_of_open_cover 1
  intro x
  obtain ⟨V, hV, hx, _, g, hg⟩ := exists_standardSmooth_affine_chart f 1 x
  exact ⟨V, hx, (topologicalKrullDim_affineOpen V hV).le.trans
    (ringKrullDim_le_one_of_standardSmooth g hg)⟩

end FLT.Mazur.FCurve
