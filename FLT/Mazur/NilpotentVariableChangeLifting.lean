/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-!
# Lifting admissible changes through nilpotent thickenings

The scaling unit lifts because units lift through nilpotent ideals. The
remaining coordinates lift by quotient surjectivity. Congruence to the identity
can be checked coefficientwise and descends through nested quotient ideals.
-/

@[expose] public noncomputable section
open WeierstrassCurve
namespace FLT.Mazur.NilpotentVariableChange
variable {R : Type*} [CommRing R]

/-- Every admissible change over a nilpotent quotient lifts to the original ring. -/
theorem exists_lift (I : Ideal R) (hI : IsNilpotent I) (C : VariableChange (R ⧸ I)) :
    ∃ D : VariableChange R, D.map (Ideal.Quotient.mk I) = C := by
  obtain ⟨u, hu⟩ := Ideal.Quotient.mk_surjective (C.u : R ⧸ I)
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective C.r
  obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective C.s
  obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective C.t
  have hunit : IsUnit u := hI.isUnit_quotient_mk_iff.mp (hu ▸ C.u.isUnit)
  refine ⟨⟨hunit.unit, r, s, t⟩, ?_⟩
  ext <;> simp only [VariableChange.map, Units.coe_map, MonoidHom.coe_ofClass,
    hunit.unit_spec, hu, hr, hs, ht]

/-- Congruence to the identity is exactly the four coefficient congruences. -/
theorem map_eq_one_iff (I : Ideal R) (C : VariableChange R) :
    C.map (Ideal.Quotient.mk I) = 1 ↔
      (C.u : R) - 1 ∈ I ∧ C.r ∈ I ∧ C.s ∈ I ∧ C.t ∈ I := by
  constructor
  · intro h
    have hu := congrArg (fun D : VariableChange (R ⧸ I) => (D.u : R ⧸ I)) h
    change Ideal.Quotient.mk I (C.u : R) = 1 at hu
    have hr := congrArg VariableChange.r h
    have hs := congrArg VariableChange.s h
    have ht := congrArg VariableChange.t h
    refine ⟨?_, ?_, ?_, ?_⟩
    · apply Ideal.Quotient.eq_zero_iff_mem.mp
      simpa [map_sub] using sub_eq_zero.mpr hu
    · exact Ideal.Quotient.eq_zero_iff_mem.mp hr
    · exact Ideal.Quotient.eq_zero_iff_mem.mp hs
    · exact Ideal.Quotient.eq_zero_iff_mem.mp ht
  · rintro ⟨hu, hr, hs, ht⟩
    have hu' := Ideal.Quotient.eq_zero_iff_mem.mpr hu
    rw [map_sub, map_one, sub_eq_zero] at hu'
    ext
    · exact hu'
    · exact Ideal.Quotient.eq_zero_iff_mem.mpr hr
    · exact Ideal.Quotient.eq_zero_iff_mem.mpr hs
    · exact Ideal.Quotient.eq_zero_iff_mem.mpr ht

/-- Membership in a larger ideal is detected after quotienting by a smaller one. -/
theorem quotient_mem_map_iff (I J : Ideal R) (hIJ : I ≤ J) (x : R) :
    Ideal.Quotient.mk I x ∈ J.map (Ideal.Quotient.mk I) ↔ x ∈ J := by
  change x ∈ (J.map (Ideal.Quotient.mk I)).comap (Ideal.Quotient.mk I) ↔ x ∈ J
  rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
    show Ideal.comap (Ideal.Quotient.mk I) ⊥ = I from Ideal.mk_ker,
    sup_eq_left.mpr hIJ]

/-- Identity congruences over nested nilpotent stages retain the original ideal. -/
theorem map_eq_one_of_quotient (I J : Ideal R) (hIJ : I ≤ J)
    (C : VariableChange R)
    (hC : (C.map (Ideal.Quotient.mk I)).map
      (Ideal.Quotient.mk (J.map (Ideal.Quotient.mk I))) = 1) :
    C.map (Ideal.Quotient.mk J) = 1 := by
  rw [map_eq_one_iff] at hC ⊢
  rcases hC with ⟨hu, hr, hs, ht⟩
  refine ⟨?_, (quotient_mem_map_iff I J hIJ _).mp hr,
    (quotient_mem_map_iff I J hIJ _).mp hs, (quotient_mem_map_iff I J hIJ _).mp ht⟩
  apply (quotient_mem_map_iff I J hIJ _).mp
  change Ideal.Quotient.mk I (C.u : R) - 1 ∈ J.map (Ideal.Quotient.mk I) at hu
  simpa only [map_sub, map_one] using hu

/-- Identity congruences persist when the ideal is enlarged. -/
theorem map_eq_one_of_le (I J : Ideal R) (hIJ : I ≤ J) (C : VariableChange R)
    (hC : C.map (Ideal.Quotient.mk I) = 1) : C.map (Ideal.Quotient.mk J) = 1 := by
  rw [map_eq_one_iff] at hC ⊢
  exact ⟨hIJ hC.1, hIJ hC.2.1, hIJ hC.2.2.1, hIJ hC.2.2.2⟩

end FLT.Mazur.NilpotentVariableChange
