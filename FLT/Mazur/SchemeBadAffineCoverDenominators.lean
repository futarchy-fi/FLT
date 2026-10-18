/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeBadAffineCover
public import FLT.Mazur.SchemeScalarIntegralBadCover
public import FLT.Mazur.SchemeOpenEnvelopeDenominators

/-!
# Denominators from the constructed affine bad charts

The original denominator ideal is a finite intersection of radical kernels
on actual affine charts of the bad locus. Products of exact kernel elements
construct original principal neighborhoods without ambient affineness.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace FLT.Mazur.SchemeBadAffineCover
open SchemeScalarPrincipalNeighborhood SchemeOpenEnvelope
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] {X : Scheme.{0}} [NoetherianSpace X]
  (s : R →+* Γ(X, ⊤)) (O : X.Opens)

/-- Original scalars on an actual affine bad chart. -/
def badChartScalar (i : (badCover O).I₀) : R →+* Γ((badCover O).X i, ⊤) :=
  (badChartMap O i).appTop.hom.comp s

/-- The full bad scalar image is the finite union of the constructed chart images. -/
theorem badImage_eq_chart_ranges :
    scalarMorphism s '' (O : Set X)ᶜ =
      ⋃ i, Set.range (scalarMorphism (badChartScalar s O i)) := by
  ext P
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨i, y, rfl⟩ := exists_badChart_lift O x hx
    apply Set.mem_iUnion.mpr
    exact ⟨i, y, by rw [badChartScalar, scalarMorphism_comp]; rfl⟩
  · intro hP
    obtain ⟨i, y, rfl⟩ := Set.mem_iUnion.mp hP
    refine ⟨badChartMap O i y, badChartMap_not_mem O i y, ?_⟩
    rw [badChartScalar, scalarMorphism_comp]
    rfl

/-- The exact denominator ideal is computed on finitely many constructed affine bad charts. -/
theorem denominatorIdeal_eq_badChart_kernels :
    denominatorIdeal s O = ⨅ i, (RingHom.ker (badChartScalar s O i)).radical := by
  have he : denominatorIdeal s O = scalarAvoidanceIdeal s O := by
    ext r
    exact (mem_scalarAvoidanceIdeal_iff s O r).symm
  rw [he, scalarAvoidanceIdeal, badImage_eq_chart_ranges, PrimeSpectrum.vanishingIdeal_iUnion]
  congr 1
  funext i
  rw [scalarMorphism_range_eq_comap, PrimeSpectrum.vanishingIdeal_range_comap]

/-- Scalars killed on every affine bad chart define a full principal neighborhood. -/
theorem basicOpen_le_of_badChart_zero (r : R)
    (hr : ∀ i, badChartScalar s O i r = 0) : X.basicOpen (s r) ≤ O := by
  change r ∈ denominatorIdeal s O
  rw [denominatorIdeal_eq_badChart_kernels, Ideal.mem_iInf]
  intro i
  exact Ideal.le_radical (hr i)

/-- Multiplying one exact kernel separator per chart keeps the unchanged original prime. -/
theorem badChart_kernel_product (P : PrimeSpectrum R) (a : (badCover O).I₀ → R)
    (ha : ∀ i, a i ∉ P.asIdeal ∧ badChartScalar s O i (a i) = 0) :
    (∏ i, a i) ∉ P.asIdeal ∧ X.basicOpen (s (∏ i, a i)) ≤ O := by
  classical
  constructor
  · intro h
    obtain ⟨i, _, hi⟩ := Ideal.IsPrime.prod_mem_iff.mp h
    exact (ha i).1 hi
  · apply basicOpen_le_of_badChart_zero
    intro i
    have hm : (∏ j, a j) ∈ RingHom.ker (badChartScalar s O i) :=
      Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem a (Finset.mem_univ i)) (ha i).2
    exact hm

end FLT.Mazur.SchemeBadAffineCover
