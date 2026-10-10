/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSplitNodalObstruction
public import FLT.Mazur.WeierstrassSplitNodalTorus
public import FLT.Mazur.WeierstrassIntegralCurveTwoChartCover
public import FLT.Mazur.WeierstrassIntegralProjectivePreimage

/-!
# The full smooth locus of a split nodal cubic over a field

The omitted affine origin is obstructed, so the actual smooth locus is
exactly the original Y chart. The torus comparison is consequently an
isomorphism of schemes, not merely a bijection of classical points.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped LaurentPolynomial

namespace FLT.Mazur.WeierstrassIntegralChart

open PolygonNodePresentation

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {K : Type u} [Field K] (a : Kˣ)

/-- A prime where Y vanishes contains the kernel of the actual origin evaluation. -/
theorem splitNodalOrigin_ker_le (p : PrimeSpectrum (Coordinate (splitNodalEquation a) 2))
    (hy : coord (splitNodalEquation a) 2 1 ∈ p.asIdeal) :
    RingHom.ker (splitNodalOriginEval a).toRingHom ≤ p.asIdeal := by
  have hx : coord (splitNodalEquation a) 2 0 ∈ p.asIdeal := by
    apply p.isPrime.mem_of_pow_mem 3
    have hr := sub_eq_zero.mp (splitNodalAffine_relation a)
    rw [← hr]
    exact p.asIdeal.add_mem (p.asIdeal.pow_mem_of_mem hy 2 (by omega))
      (p.asIdeal.mul_mem_left _ hy)
  let q := Ideal.Quotient.mkₐ K p.asIdeal
  have h : q = (Algebra.ofId K _).comp (splitNodalOriginEval a) := by
    apply hom_ext (S := Coordinate (splitNodalEquation a) 2 ⧸ p.asIdeal)
    intro i
    fin_cases i
    · simpa [q] using Ideal.Quotient.eq_zero_iff_mem.mpr hx
    · simpa [q] using Ideal.Quotient.eq_zero_iff_mem.mpr hy
    · simp
  intro z hz
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change q z = 0
  rw [h, AlgHom.comp_apply, show splitNodalOriginEval a z = 0 from hz, map_zero]

/-- A smooth point of the original finite chart has nonvanishing Y coordinate. -/
theorem splitNodalAffine_smooth_y (p : chartScheme (splitNodalEquation a) 2)
    (hp : p ∈ (chartStructure (splitNodalEquation a) 2).smoothLocus) :
    coord (splitNodalEquation a) 2 1 ∉ p.asIdeal := by
  intro hy
  exact smooth_disjoint_origin (splitNodalOriginEval a)
    (splitNodalOrigin_not_formallySmooth a) ((spec_smooth_iff p).mp hp)
    (splitNodalOrigin_ker_le a p hy)

/-- Every scheme-theoretically smooth point lies in the original torus chart. -/
theorem splitNodalField_smooth_range :
    (integralSmoothOpen (splitNodalEquation a) : Set (integralCurve (splitNodalEquation a))) =
      Set.range (integralCurveChart (splitNodalEquation a) 1) := by
  apply Set.Subset.antisymm
  · intro x hx
    rcases integralCurve_yz_cover (splitNodalEquation a) x with hy | ⟨z, rfl⟩
    · exact hy
    · apply integralCurveChart_mem_range (splitNodalEquation a) 2 1 z
      apply splitNodalAffine_smooth_y a z
      have h := integralCurveChart_preimage_smooth (splitNodalEquation a) 2
      exact h.le hx
  · exact splitNodalChart_range_smooth a

/-- The existing torus comparison covers the entire smooth locus over a field. -/
theorem splitNodalField_torusToSmooth_surjective :
    Function.Surjective (splitNodalTorusToSmooth a) := by
  intro x
  obtain ⟨y, hy⟩ := (splitNodalField_smooth_range a).le x.property
  obtain ⟨z, rfl⟩ := (splitNodalTorusIso a).hom.surjective y
  refine ⟨z, ?_⟩
  apply (integralSmoothOpen (splitNodalEquation a)).ι.isOpenEmbedding.injective
  change (splitNodalTorusToSmooth a ≫ (integralSmoothOpen (splitNodalEquation a)).ι) z = _
  rw [splitNodalTorusToSmooth_inclusion]
  exact hy

/-- The actual torus inclusion is an isomorphism onto the full smooth locus over a field. -/
instance splitNodalField_torusToSmooth_isIso : IsIso (splitNodalTorusToSmooth a) := by
  apply isIso_of_isOpenImmersion_of_opensRange_eq_top
  apply TopologicalSpace.Opens.ext
  exact (splitNodalField_torusToSmooth_surjective a).range_eq

/-- The full smooth locus of the original split nodal field cubic is the torus. -/
def splitNodalFieldSmoothIso : Spec (.of K[T;T⁻¹]) ≅
    (integralSmoothOpen (splitNodalEquation a)).toScheme :=
  asIso (splitNodalTorusToSmooth a)

end FLT.Mazur.WeierstrassIntegralChart
