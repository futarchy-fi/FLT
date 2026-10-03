/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.AdicLocalizationBasis
public import Mathlib.RingTheory.AdicCompletion.Topology

/-! # Separation and continuity for the coefficient topology on a localization -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable {R : Type*} [CommRing R] (r : R) (S : Type*) [CommRing S] [Algebra R S]

/-- Separation of integral lattices follows from separation of R and injectivity. -/
theorem adicLocalization_eq_zero_of_mem [IsHausdorff (Ideal.span {r}) R]
    (hinj : Function.Injective (algebraMap R S)) (x : S)
    (hx : ∀ n, x ∈ adicLocalizationLattice r S n) : x = 0 := by
  obtain ⟨a, ha⟩ := (mem_adicLocalizationLattice r S 0 x).mp (hx 0)
  simp only [pow_zero, one_mul] at ha
  have hz : a = 0 := by
    apply IsHausdorff.haus' (I := Ideal.span {r})
    intro n
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton]
    obtain ⟨b, hb⟩ := (mem_adicLocalizationLattice r S n x).mp (hx n)
    exact ⟨b, hinj (ha.trans hb.symm)⟩
  rw [← ha, hz, map_zero]

variable [IsLocalization.Away r S]

/-- The lattice coefficient topology is a ring topology. -/
theorem adicLocalization_isTopologicalRing :
    let := adicLocalizationTopology r S
    IsTopologicalRing S :=
  (adicLocalizationBasis r S).toRingFilterBasis.isTopologicalRing

/-- The localized coefficient topology is Hausdorff whenever the integral map is injective. -/
theorem adicLocalization_t2Space [IsHausdorff (Ideal.span {r}) R]
    (hinj : Function.Injective (algebraMap R S)) :
    let := adicLocalizationTopology r S
    T2Space S := by
  let := adicLocalizationTopology r S
  rw [(adicLocalizationBasis r S).toRingFilterBasis.t2Space_iff_sInter_subset rfl]
  intro x hx
  apply adicLocalization_eq_zero_of_mem r S hinj x
  intro n
  exact hx _ ⟨n, rfl⟩

/-- The integral map is continuous from the parameter-adic topology. -/
theorem adicLocalization_algebraMap_continuous [TopologicalSpace R] [IsTopologicalRing R]
    (hR : IsAdic (Ideal.span {r})) :
    let := adicLocalizationTopology r S
    Continuous (algebraMap R S) := by
  let := adicLocalizationTopology r S
  let := adicLocalization_isTopologicalRing r S
  apply continuous_of_continuousAt_zero (algebraMap R S)
  rw [ContinuousAt, map_zero]
  apply (hR.hasBasis_nhds_zero.tendsto_iff (adicLocalization_hasBasis_nhds_zero r S)).mpr
  intro n _
  refine ⟨n, trivial, ?_⟩
  intro a ha
  simp only [Ideal.span_singleton_pow, SetLike.mem_coe, Ideal.mem_span_singleton] at ha
  obtain ⟨b, rfl⟩ := ha
  exact (mem_adicLocalizationLattice r S n _).mpr ⟨b, rfl⟩

/-- A lattice-preserving ring map is continuous in the localized coefficient topologies. -/
theorem adicLocalization_continuous_of_lattice {R' T : Type*} [CommRing R'] [CommRing T]
    (r' : R') [Algebra R' T] [IsLocalization.Away r' T] (f : S →+* T)
    (hf : ∀ n x, x ∈ adicLocalizationLattice r S n →
      f x ∈ adicLocalizationLattice r' T n) :
    let := adicLocalizationTopology r S
    let := adicLocalizationTopology r' T
    Continuous f := by
  let := adicLocalizationTopology r S
  let := adicLocalizationTopology r' T
  let := adicLocalization_isTopologicalRing r S
  let := adicLocalization_isTopologicalRing r' T
  apply continuous_of_continuousAt_zero f
  rw [ContinuousAt, map_zero]
  exact ((adicLocalization_hasBasis_nhds_zero r S).tendsto_iff
    (adicLocalization_hasBasis_nhds_zero r' T)).mpr fun n _ ↦ ⟨n, trivial, hf n⟩

end PadicHodgeTheory
