/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXMiddleLines
public import FLT.Mazur.WeierstrassModificationXConicGeometry
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Closed components of the successive middle fiber

The original conic and two horizontal tangent lines are actual closed
subschemes covering the fiber. Their kernels retain their scheme structures.
-/

@[expose] public noncomputable section
open Polynomial AlgebraicGeometry
namespace FLT.Mazur.WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open WeierstrassModificationX
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (c : R) (h2 : W.a₂ = 0)
local notation "A" => Coordinate W 0 0 0 0 c
local notation "T" => coord W 0 0 0 0 c 0
local notation "V" => coord W 0 0 0 0 c 1
local notation "U" => coord W 0 0 0 0 c 2

/-- The retained conic is an actual closed subscheme of the successive fiber. -/
def middleConicImmersion : Spec (.of (ConicCoordinate W.a₁ c)) ⟶ Spec (.of A) :=
  Spec.map (CommRingCat.ofHom (middleConicMap W c h2).toRingHom)

instance middleConicImmersion_isClosedImmersion :
    IsClosedImmersion (middleConicImmersion W c h2) :=
  IsClosedImmersion.spec_of_surjective _ (middleConicMap_surjective W c h2)

/-- A specified tangent root gives its actual horizontal closed line. -/
def middleLineImmersion (r : R) (hr : r * (r + W.a₁) = 0) :
    Spec (.of R[X]) ⟶ Spec (.of A) :=
  Spec.map (CommRingCat.ofHom (middleLineMap W c h2 r hr).toRingHom)

instance middleLineImmersion_isClosedImmersion (r : R) (hr : r * (r + W.a₁) = 0) :
    IsClosedImmersion (middleLineImmersion W c h2 r hr) :=
  IsClosedImmersion.spec_of_surjective _ (middleLineMap_surjective W c h2 r hr)

/-- The conic is supported at exactly u = 0. -/
theorem range_middleConicImmersion : Set.range (middleConicImmersion W c h2) =
    PrimeSpectrum.zeroLocus (Ideal.span {U}) := by
  rw [← middleConicMap_ker W c h2]
  exact range_comap_of_surjective _ _ (middleConicMap_surjective W c h2)

/-- The specified tangent line is supported at exactly t = 0 and v = r. -/
theorem range_middleLineImmersion (r : R) (hr : r * (r + W.a₁) = 0) :
    Set.range (middleLineImmersion W c h2 r hr) =
      PrimeSpectrum.zeroLocus (middleLineIdeal W c r) := by
  rw [← middleLineMap_ker W c h2 r hr]
  exact range_comap_of_surjective _ _ (middleLineMap_surjective W c h2 r hr)

/-- The three actual closed subschemes cover the entire successive middle fiber. -/
theorem middle_components_cover (p : Spec (.of A)) :
    p ∈ Set.range (middleConicImmersion W c h2) ∨
    p ∈ Set.range (middleLineImmersion W c h2 0 (middle_first_root W)) ∨
    p ∈ Set.range (middleLineImmersion W c h2 (-W.a₁) (middle_second_root W)) := by
  have htu : T * U ∈ p.asIdeal := by
    rw [incidence, map_zero]
    exact p.asIdeal.zero_mem
  rw [range_middleConicImmersion, range_middleLineImmersion, range_middleLineImmersion]
  rcases p.isPrime.mem_or_mem htu with ht | hu
  · have hv : V * (V + algebraMap R A W.a₁) ∈ p.asIdeal := by
      rw [sub_eq_zero.mp (middle_conic_relation W c h2)]
      rw [pow_two]
      exact p.asIdeal.mul_mem_left _ (p.asIdeal.mul_mem_left _ ht)
    rcases p.isPrime.mem_or_mem hv with h0 | h1
    · right; left
      apply Ideal.span_le.mpr
      intro z hz
      rcases Set.mem_insert_iff.mp hz with rfl | hz
      · exact ht
      · obtain rfl := Set.mem_singleton_iff.mp hz
        simpa using h0
    · right; right
      apply Ideal.span_le.mpr
      intro z hz
      rcases Set.mem_insert_iff.mp hz with rfl | hz
      · exact ht
      · obtain rfl := Set.mem_singleton_iff.mp hz
        simpa using h1
  · exact Or.inl (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hu))

/-- The conic in this cover has its actual smooth structure over the base. -/
theorem middle_conic_smooth (ha : IsUnit W.a₁) : Smooth (conicStructure W.a₁ c) :=
  conicStructure_smooth W.a₁ c ha

end FLT.Mazur.WeierstrassSuccessiveX
