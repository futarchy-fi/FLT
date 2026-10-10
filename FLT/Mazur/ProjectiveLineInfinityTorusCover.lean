/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.ProjectiveLineInfinityTorusAlgebra
public import FLT.Mazur.ProjectiveLineCharts
public import FLT.Mazur.SchemeOpenPushoutIntersection

/-!
# The left affine chart and translated infinity torus cover the projective line

The torus is the exact right-chart open 1+a*w, including the point w=0.
Its omitted point already lies in the left chart.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits Polynomial
open scoped LaurentPolynomial
namespace FLT.Mazur.ProjectiveLine
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] (a : Kˣ)

/-- The entire Laurent torus inside the right affine chart. -/
def infinityTorusToRight : overlap K ⟶ chart K :=
  Spec.map (CommRingCat.ofHom (infinityTorusMap a).toRingHom)

/-- This is the actual principal-open chart supplied by the localization equivalence. -/
theorem infinityTorusToRight_eq_chart : infinityTorusToRight a =
    PrincipalOpenTransport.chart (infinityTorusPolynomial a) (infinityTorusEquiv a) := by
  change Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (RingHom.ext (fun p => (infinityTorusEquiv_base_map a p).symm))

instance infinityTorusToRight_isOpenImmersion : IsOpenImmersion (infinityTorusToRight a) := by
  rw [infinityTorusToRight_eq_chart]
  infer_instance

/-- The full torus image in the right chart is precisely 1+a*w nonzero. -/
theorem infinityTorusToRight_range : Set.range (infinityTorusToRight a) =
    (PrimeSpectrum.basicOpen (infinityTorusPolynomial a) : Set (PrimeSpectrum K[X])) := by
  rw [infinityTorusToRight_eq_chart]
  exact PrincipalOpenTransport.chart_range _ _

/-- The translated infinity torus as an open chart of the projective line. -/
def infinityTorusChart : overlap K ⟶ scheme K := infinityTorusToRight a ≫ right K

instance infinityTorusChart_isOpenImmersion : IsOpenImmersion (infinityTorusChart a) :=
  inferInstanceAs (IsOpenImmersion (_ ≫ _))

/-- The standard right overlap is exactly the punctured right affine line. -/
theorem overlapRight_range_basicOpen : Set.range (overlapRight K) =
    (PrimeSpectrum.basicOpen (X : K[X]) : Set (PrimeSpectrum K[X])) := by
  have h : Set.range (overlapRight K) = Set.range (overlapLeft K) := by
    change Set.range (fun z => overlapLeft K ((inversion K).hom z)) = _
    simpa only [Function.comp_def, Scheme.Hom.homeomorph_apply] using
      (inversion K).hom.homeomorph.surjective.range_comp (overlapLeft K)
  rw [h]
  exact PrimeSpectrum.localization_away_comap_range K[T;T⁻¹] X

/-- The inverse image of the full left chart is the punctured right chart. -/
theorem right_preimage_left_basicOpen : (right K) ⁻¹' Set.range (left K) =
    (PrimeSpectrum.basicOpen (X : K[X]) : Set (PrimeSpectrum K[X])) := by
  rw [show (right K) ⁻¹' Set.range (left K) = Set.range (overlapRight K) from
    SchemeOpenPushout.inr_preimage_inl (overlapLeft K) (overlapRight K)]
  exact overlapRight_range_basicOpen

/-- The omitted locus of the translated torus is already in the standard overlap. -/
theorem infinityTorus_affine_cover (x : PrimeSpectrum K[X]) :
    x ∈ PrimeSpectrum.basicOpen (X : K[X]) ∨
      x ∈ PrimeSpectrum.basicOpen (infinityTorusPolynomial a) := by
  by_cases hx : X ∈ x.asIdeal
  · right
    rw [PrimeSpectrum.mem_basicOpen]
    intro hf
    have hm := x.asIdeal.mul_mem_left (C (a : K)) hx
    have h1 : (1 : K[X]) ∈ x.asIdeal := by
      simpa only [infinityTorusPolynomial, add_sub_cancel_right] using x.asIdeal.sub_mem hf hm
    exact x.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h1 isUnit_one)
  · exact Or.inl hx

/-- The full original left line and the translated infinity torus exhaust the projective line. -/
theorem infinityTorus_charts_cover (x : scheme K) :
    (∃ y : chart K, left K y = x) ∨ ∃ z : overlap K, infinityTorusChart a z = x := by
  rcases charts_cover K x with h | ⟨y, rfl⟩
  · exact Or.inl h
  · rcases infinityTorus_affine_cover a y with hy | hy
    · left
      have h : right K y ∈ Set.range (left K) := by
        change y ∈ (right K) ⁻¹' Set.range (left K)
        rw [right_preimage_left_basicOpen]
        exact hy
      exact h
    · right
      have hy' : y ∈ Set.range (infinityTorusToRight a) := by
        rw [infinityTorusToRight_range]
        exact hy
      obtain ⟨z, rfl⟩ := hy'
      exact ⟨z, rfl⟩

/-- The torus inclusion respects the original coefficient structure. -/
@[reassoc] theorem infinityTorusChart_toBase : infinityTorusChart a ≫ toBase K =
    Spec.map (CommRingCat.ofHom (algebraMap K K[T;T⁻¹])) := by
  rw [infinityTorusChart, Category.assoc, right_toBase, infinityTorusToRight,
    chartToBase, ← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (RingHom.ext (infinityTorusMap a).commutes)

end FLT.Mazur.ProjectiveLine
