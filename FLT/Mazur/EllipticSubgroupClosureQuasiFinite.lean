/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticSubgroupPointLocalization
public import FLT.Mazur.EllipticSubgroupClosureProperties
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-!
# Finite fibers of the glued subgroup closure

The individual point quotients cover each closure chart. Their maps to the base
are principal open immersions, so each contributes at most one point to a fiber.
For a finite subgroup this proves quasi-finiteness of the actual glued closure.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.EllipticSubgroupChart

variable {K : Type*} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)
  (H : AddSubgroup (W.map (algebraMap A K)).toProjective.Point) (j : Fin 3)

/-- The individual point closure inside an affine subgroup closure chart. -/
abbrev pointClosureChart (P : Index A W H j) :=
  Spec (.of (AffineGenericClosure.Coordinate (pointEvaluation A W H j P)))

/-- The closed immersion defined by the individual generic point kernel. -/
def pointClosureToChart (P : Index A W H j) :
    pointClosureChart A W H j P ⟶ closureChart A W H j :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk _))

instance pointClosureToChart_isClosedImmersion (P : Index A W H j) :
    IsClosedImmersion (pointClosureToChart A W H j P) :=
  IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

/-- The structural map on an individual point closure is the base localization map. -/
theorem pointClosureToChart_toBase (P : Index A W H j) :
    pointClosureToChart A W H j P ≫ closureChartToBase A W H j =
      Spec.map (CommRingCat.ofHom (algebraMap A
        (AffineGenericClosure.Coordinate (pointEvaluation A W H j P)))) := by
  rw [pointClosureToChart, closureChartToBase, ← Spec.map_comp]
  rfl

/-- An individual point closure is a principal open of the base. -/
instance pointClosureToBase_isOpenImmersion (P : Index A W H j) :
    IsOpenImmersion (pointClosureToChart A W H j P ≫ closureChartToBase A W H j) := by
  rw [pointClosureToChart_toBase]
  exact IsOpenImmersion.of_isLocalization ((primitiveLift A W P.1.1).coords j)

/-- The individual point closures cover every prime of a finite subgroup chart. -/
theorem pointClosure_charts_cover [Finite H] (x : closureChart A W H j) :
    ∃ (P : Index A W H j) (y : pointClosureChart A W H j P),
      pointClosureToChart A W H j P y = x := by
  obtain ⟨P, hP, _⟩ := exists_point_kernel_le A W H j x
  have hx : x ∈ Set.range (PrimeSpectrum.comap
      (Ideal.Quotient.mk (RingHom.ker (pointEvaluation A W H j P).toRingHom))) := by
    rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective]
    change RingHom.ker (Ideal.Quotient.mk _) ≤ x.asIdeal
    simpa only [Ideal.mk_ker] using hP
  obtain ⟨y, hy⟩ := hx
  exact ⟨P, y, hy⟩

/-- Each affine subgroup closure has finite fibers over the valuation ring. -/
theorem closureChartToBase_finite_fiber [Finite H] (x : Spec (.of A)) :
    (closureChartToBase A W H j ⁻¹' {x}).Finite := by
  let g := pointClosureToChart A W H j
  let f := closureChartToBase A W H j
  have hf (P : Index A W H j) : ((g P ≫ f) ⁻¹' {x}).Finite :=
    (Set.finite_singleton x).preimage (g P ≫ f).isOpenEmbedding.injective.injOn
  apply (Set.finite_iUnion fun P => (hf P).image (g P)).subset
  intro y hy
  obtain ⟨P, z, rfl⟩ := pointClosure_charts_cover A W H j y
  exact Set.mem_iUnion.mpr ⟨P, z, hy, rfl⟩

/-- Finite point sets give locally quasi-finite affine closure charts. -/
instance closureChartToBase_locallyQuasiFinite [Finite H] :
    LocallyQuasiFinite (closureChartToBase A W H j) :=
  LocallyQuasiFinite.of_finite_preimage_singleton _
    (closureChartToBase_finite_fiber A W H j)

/-- Quasi-finiteness descends to the actual glued subgroup closure. -/
instance closureToBase_locallyQuasiFinite [Finite H] (k : Fin 3) :
    LocallyQuasiFinite (closureToBase A W H j k) := by
  let _ := HasRingHomProperty.instIsZariskiLocalAtSource
    (P := @LocallyQuasiFinite) (Q := RingHom.QuasiFinite)
  exact closureToBase_property A W H j k (@LocallyQuasiFinite) inferInstance inferInstance

end FLT.Mazur.EllipticSubgroupChart
