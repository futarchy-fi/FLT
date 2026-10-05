/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicScheme
public import FLT.Mazur.ProjectiveSpaceReindex
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-!
# The two-chart cover of the projective Weierstrass locus

On the homogeneous cubic, simultaneous vanishing of Y and Z forces X to
vanish at every prime ideal. Thus its projective zero locus is covered by
the two charts used in CubicScheme. This is a statement about the actual
Proj topological space; the scheme-level projective embedding is separate.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial

namespace WeierstrassCurve.CubicCharts

attribute [local instance] MvPolynomial.gradedAlgebra

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The ordinary chart equation is the dehomogenization Z=1. -/
theorem affine_equation_eq_dehomogenization :
    equation W false =
      eval₂Hom C ![X 0, X 1, 1] W.toProjective.polynomial := by
  simp [equation, Projective.polynomial]

/-- The infinity equation is the dehomogenization Y=1. -/
theorem infinity_equation_eq_dehomogenization :
    equation W true =
      eval₂Hom C ![X 0, 1, X 1] W.toProjective.polynomial :=
  InfinityChart.equation_eq_dehomogenization W

/-- No homogeneous prime containing the cubic can contain Y and Z without X.
This argument works over arbitrary coefficient rings. -/
theorem X_mem_of_Y_Z_mem (I : Ideal (MvPolynomial (Fin 3) R)) [I.IsPrime]
    (hW : W.toProjective.polynomial ∈ I)
    (hY : X (1 : Fin 3) ∈ I) (hZ : X (2 : Fin 3) ∈ I) :
    X (0 : Fin 3) ∈ I := by
  have hy := Ideal.Quotient.eq_zero_iff_mem.mpr hY
  have hz := Ideal.Quotient.eq_zero_iff_mem.mpr hZ
  have hw := Ideal.Quotient.eq_zero_iff_mem.mpr hW
  have hx : (Ideal.Quotient.mk I (X (0 : Fin 3))) ^ 3 = 0 := by
    simpa [Projective.polynomial, map_sub, map_add, map_mul, map_pow, hy, hz] using hw
  exact Ideal.Quotient.eq_zero_iff_mem.mp (eq_zero_of_pow_eq_zero hx)

/-- Every point of the projective cubic lies in one of the two gluing charts. -/
theorem projective_locus_two_chart_cover
    (p : FLT.Mazur.ProjectiveSpace.space R (Fin 3))
    (hp : W.toProjective.polynomial ∈ p.asHomogeneousIdeal.toIdeal) :
    p ∈ FLT.Mazur.ProjectiveSpace.chart R (Fin 3) 1 ∨
      p ∈ FLT.Mazur.ProjectiveSpace.chart R (Fin 3) 2 := by
  let I := p.asHomogeneousIdeal.toIdeal
  have : I.IsPrime := p.isPrime
  change X (1 : Fin 3) ∉ I ∨ X (2 : Fin 3) ∉ I
  by_contra h
  push Not at h
  have hx := X_mem_of_Y_Z_mem W I hp h.1 h.2
  obtain ⟨i, hi⟩ := FLT.Mazur.ProjectiveSpace.exists_mem_chart R (Fin 3) p
  change X i ∉ I at hi
  fin_cases i
  · exact hi hx
  · exact hi h.1
  · exact hi h.2

/-- Coordinate order for embedding each affine chart in the common plane:
the ordinary chart is [x:y:1], and the infinity chart is [u:1:v]. -/
def projectiveCoordinateOrder (b : Bool) : Fin 3 ≃ Fin 3 :=
  if b then Equiv.swap 0 1 else (Equiv.swap 0 1).trans (Equiv.swap 1 2)

/-- The homogeneous cubic pulls back to precisely the chosen chart equation
under the coordinate order used by its projective immersion. -/
theorem equation_in_projective_coordinates (b : Bool) :
    eval₂Hom C (fun i : Fin 3 ↦
      Fin.cases (1 : MvPolynomial (Fin 2) R) X ((projectiveCoordinateOrder b).symm i))
        W.toProjective.polynomial = equation W b := by
  cases b <;> simp [projectiveCoordinateOrder, Equiv.swap_apply_def,
    Projective.polynomial, equation, InfinityChart.equation] <;> rfl

/-- The actual morphism from either quotient chart to the same projective plane. -/
def chartToProjective (b : Bool) :
    chart W b ⟶ FLT.Mazur.ProjectiveSpace.space R (Fin 3) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {equation W b}))) ≫
    FLT.Mazur.ProjectiveSpace.affineChartEmbedding R 2 ≫
      (FLT.Mazur.ProjectiveSpace.reindexIso R (projectiveCoordinateOrder b)).hom

/-- Each chart map is an immersion: a closed affine hypersurface followed by
an open affine chart and a projective coordinate permutation. -/
instance chartToProjective_isImmersion (b : Bool) : IsImmersion (chartToProjective W b) := by
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (Ideal.span {equation W b})))) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  unfold chartToProjective chart
  infer_instance

/-- Both projective chart morphisms preserve the coefficient base. -/
@[reassoc] theorem chartToProjective_baseProjection (b : Bool) :
    chartToProjective W b ≫ FLT.Mazur.ProjectiveSpace.baseProjection R (Fin 3) =
      chartToBase W b := by
  unfold chartToProjective chartToBase chart
  simp only [Category.assoc, FLT.Mazur.ProjectiveSpace.reindexIso_baseProjection,
    FLT.Mazur.ProjectiveSpace.affineChartEmbedding_baseProjection]
  rw [← Spec.map_comp]
  rfl

end WeierstrassCurve.CubicCharts
