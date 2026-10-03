/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology

/-! # Integral lattices define the coefficient topology after inverting a parameter -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable {R : Type*} [CommRing R] (r : R) (S : Type*) [CommRing S] [Algebra R S]

/-- The image of r^n R in an R-algebra, as an additive subgroup. -/
def adicLocalizationLattice (n : ℕ) : AddSubgroup S :=
  (Ideal.span {r ^ n}).toAddSubgroup.map (algebraMap R S).toAddMonoidHom

/-- Lattice membership is an integral multiple of the indicated parameter power. -/
theorem mem_adicLocalizationLattice (n : ℕ) (x : S) :
    x ∈ adicLocalizationLattice r S n ↔ ∃ a : R, algebraMap R S (r ^ n * a) = x := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton.mp hy
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨r ^ n * a, Ideal.mem_span_singleton.mpr (dvd_mul_right _ _), rfl⟩

/-- Higher powers give smaller integral lattices. -/
theorem adicLocalizationLattice_antitone : Antitone (adicLocalizationLattice r S) := by
  intro m n h x hx
  obtain ⟨a, rfl⟩ := (mem_adicLocalizationLattice r S n x).mp hx
  obtain ⟨b, hb⟩ := pow_dvd_pow r h
  exact (mem_adicLocalizationLattice r S m _).mpr ⟨b * a, by rw [hb, mul_assoc]⟩

variable [IsLocalization.Away r S]

/-- Denominator clearing proves the ring-basis axioms for the integral lattices. -/
theorem adicLocalizationBasis : RingSubgroupsBasis (adicLocalizationLattice r S) :=
  RingSubgroupsBasis.of_comm _
    (fun i j ↦ ⟨max i j, le_inf (adicLocalizationLattice_antitone r S (le_max_left _ _))
      (adicLocalizationLattice_antitone r S (le_max_right _ _))⟩)
    (by
      intro n
      refine ⟨n, ?_⟩
      rintro x ⟨y, hy, z, hz, rfl⟩
      obtain ⟨a, rfl⟩ := (mem_adicLocalizationLattice r S n y).mp hy
      obtain ⟨b, rfl⟩ := (mem_adicLocalizationLattice r S n z).mp hz
      apply (mem_adicLocalizationLattice r S n _).mpr
      exact ⟨a * (r ^ n * b), by simp only [map_mul, mul_assoc]⟩)
    (by
      intro x n
      obtain ⟨k, a, ha⟩ := IsLocalization.Away.surj r x
      refine ⟨k + n, ?_⟩
      intro y hy
      obtain ⟨b, rfl⟩ := (mem_adicLocalizationLattice r S (k + n) y).mp hy
      apply (mem_adicLocalizationLattice r S n _).mpr
      refine ⟨a * b, ?_⟩
      calc algebraMap R S (r ^ n * (a * b)) =
            algebraMap R S a * (algebraMap R S (r ^ n) * algebraMap R S b) := by
              simp only [map_mul]; ring
           _ = x * algebraMap R S (r ^ (k + n) * b) := by
              rw [← ha]
              simp only [pow_add, map_mul, map_pow]
              ring)

/-- The coefficient topology after inverting r; its neighborhoods remain integral lattices. -/
@[instance_reducible]
def adicLocalizationTopology : TopologicalSpace S := (adicLocalizationBasis r S).topology

/-- The defining basis of neighborhoods of zero in the coefficient topology. -/
theorem adicLocalization_hasBasis_nhds_zero :
    Filter.HasBasis (@nhds S (adicLocalizationTopology r S) 0) (fun _ : ℕ ↦ True)
      (fun n ↦ (adicLocalizationLattice r S n : Set S)) :=
  (adicLocalizationBasis r S).hasBasis_nhds_zero

end PadicHodgeTheory
