/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.RingTheory.Flat.PresentationKernelIntersection
public import Mathlib.RingTheory.Nakayama
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Lift relation generators through an arbitrary radical base ideal -/

@[expose] public noncomputable section

namespace Ideal

variable {S : Type*} [CommRing S]

/-- Nakayama lifts equality of relation ideals modulo a radical ideal when the
kernel intersection is the corresponding product. -/
theorem eq_of_map_quotient_eq_of_inf_eq_mul {I J L : Ideal S}
    (hI : I.FG) (hL : L ≤ jacobson (⊥ : Ideal S)) (hJI : J ≤ I)
    (hinf : I ⊓ L = L * I)
    (hgen : J.map (Quotient.mk L) = I.map (Quotient.mk L)) : J = I := by
  apply le_antisymm hJI
  apply Submodule.le_of_le_smul_of_le_jacobson_bot hI hL
  have hle : I ≤ J ⊔ L := by
    have h := congrArg (Ideal.comap (Quotient.mk L)) hgen
    simp only [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective] at h
    change J ⊔ RingHom.ker (Quotient.mk L) = I ⊔ RingHom.ker (Quotient.mk L) at h
    rw [Ideal.mk_ker] at h
    exact le_sup_left.trans h.ge
  intro s hs
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp (hle hs)
  have hbI : b ∈ I := (I.add_mem_iff_right (hJI ha)).mp hs
  have hbprod : b ∈ L * I := hinf ▸ (show b ∈ I ⊓ L from ⟨hbI, hb⟩)
  exact Submodule.mem_sup.mpr ⟨a, ha, b, hbprod, rfl⟩

end Ideal

namespace AlgHom

variable {R S A : Type*} [CommRing R] [CommRing S] [CommRing A]
  [Algebra R S] [Algebra R A] [Module.Flat R A]

/-- Generators of the reduced kernel lift to generators of the whole original kernel.
The base ideal is arbitrary; no principal or regular-element hypothesis is needed. -/
theorem exists_kernel_generators_of_flat_quotient
    (f : S →ₐ[R] A) (hf : Function.Surjective f) (hker : (RingHom.ker f).FG)
    (J : Ideal R) (hJ : J.map (algebraMap R S) ≤ Ideal.jacobson (⊥ : Ideal S))
    {ι : Type*} (v : ι → S ⧸ J.map (algebraMap R S))
    (hv : Ideal.span (Set.range v) =
      (RingHom.ker f).map (Ideal.Quotient.mk (J.map (algebraMap R S)))) :
    ∃ w : ι → S, (∀ i, Ideal.Quotient.mk (J.map (algebraMap R S)) (w i) = v i) ∧
      Ideal.span (Set.range w) = RingHom.ker f := by
  have hmem (i) : v i ∈ (RingHom.ker f).map (Ideal.Quotient.mk (J.map (algebraMap R S))) := by
    rw [← hv]
    exact Ideal.subset_span ⟨i, rfl⟩
  choose w hw heq using fun i ↦
    (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp (hmem i)
  refine ⟨w, heq, Ideal.eq_of_map_quotient_eq_of_inf_eq_mul hker hJ
    (Ideal.span_le.mpr (Set.range_subset_iff.mpr hw))
    (f.ker_inf_map_eq_mul_of_flat hf J) ?_⟩
  rw [Ideal.map_span, ← Set.range_comp]
  simpa only [Function.comp_def, heq] using hv

end AlgHom
