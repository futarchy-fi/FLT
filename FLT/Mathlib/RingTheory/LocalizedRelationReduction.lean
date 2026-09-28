/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.RingTheory.LocalizedPresentation

/-! # Transporting reduced relations to a localized presentation -/

@[expose] public noncomputable section

namespace AlgHom

variable {R S A : Type*} [CommRing R] [CommRing S] [CommRing A]
  [Algebra R S] [Algebra R A]

/-- Surjectivity modulo a radical parameter implies surjectivity onto a finite algebra. -/
theorem surjective_of_modPrincipal [Module.Finite R A]
    (f : S →ₐ[R] A) (p : R) (hp : p ∈ Ideal.jacobson (⊥ : Ideal R))
    (hf : Function.Surjective (f.modPrincipal p)) : Function.Surjective f := by
  change Function.Surjective f.toLinearMap
  rw [← LinearMap.range_eq_top]
  apply top_unique
  apply Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top
    (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hp))
  intro a _
  obtain ⟨s, hs⟩ := hf (Ideal.Quotient.mk _ a)
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective s
  have ha : a - f s ∈ Ideal.span {algebraMap R A p} := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub, ← modPrincipal_mk, hs, sub_self]
  apply Submodule.mem_sup.mpr
  refine ⟨f s, ⟨s, rfl⟩, a - f s, ?_, add_sub_cancel _ _⟩
  rw [Ideal.smul_top_eq_map]
  change a - f s ∈ (Ideal.span {p}).map (algebraMap R A)
  simpa only [Ideal.map_span, Set.image_singleton] using ha

variable [IsLocalRing A]

/-- Reduction of the localized kernel is the image of the reduced original kernel. -/
theorem ker_localizeAtMaximal_modPrincipal (f : S →ₐ[R] A)
    (hf : Function.Surjective f) (p : R) :
    RingHom.ker (f.localizeAtMaximal.modPrincipal p) =
      (RingHom.ker (f.modPrincipal p)).map
        ((IsScalarTower.toAlgHom R S f.localizedSource).modPrincipal p) := by
  rw [ker_modPrincipal _ (f.localizeAtMaximal_surjective hf),
    ker_localizeAtMaximal, ker_modPrincipal _ hf]
  change ((RingHom.ker f).map (algebraMap S f.localizedSource)).map
      (Ideal.Quotient.mk _) =
    ((RingHom.ker f).map (Ideal.Quotient.mk _)).map
      ((IsScalarTower.toAlgHom R S f.localizedSource).modPrincipal p).toRingHom
  rw [Ideal.map_map, Ideal.map_map]
  rfl

/-- A reduced polynomial relation family can be localized before applying flat lifting. -/
theorem exists_localized_quotient_equiv_of_flat_of_reduced_relations
    [IsNoetherianRing S] [Module.Flat R A]
    (f : S →ₐ[R] A) (hf : Function.Surjective f) {p : R} (hp : IsRegular p)
    (hpA : algebraMap R A p ∈ IsLocalRing.maximalIdeal A) {n : ℕ}
    (r : Fin n → S ⧸ Ideal.span {algebraMap R S p})
    (hr : Ideal.span (Set.range r) = RingHom.ker (f.modPrincipal p)) :
    ∃ (g : Fin n → f.localizedSource)
      (e : (f.localizedSource ⧸ Ideal.span (Set.range g)) ≃ₐ[R] A),
      ∀ s, e (Ideal.Quotient.mk _ s) = f.localizeAtMaximal s := by
  let q := (IsScalarTower.toAlgHom R S f.localizedSource).modPrincipal p
  have hgen : Ideal.span (Set.range (fun i ↦ q (r i))) =
      RingHom.ker (f.localizeAtMaximal.modPrincipal p) := by
    rw [f.ker_localizeAtMaximal_modPrincipal hf, ← hr, Ideal.map_span, ← Set.range_comp]
    rfl
  obtain ⟨g, e, _, he⟩ :=
    f.exists_localized_quotient_equiv_of_flat_of_modPrincipal hf hp hpA _ hgen
  exact ⟨g, e, he⟩

end AlgHom
