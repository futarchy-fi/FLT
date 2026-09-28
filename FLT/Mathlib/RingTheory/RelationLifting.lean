/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Nakayama
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Lifting generators of relation ideals

If multiplication by `p` is injective on a quotient, its relation ideal is
`p`-saturated. Nakayama then upgrades generators modulo `p` to generators of
the entire relation ideal, provided `p` belongs to the Jacobson radical.
This supplies the descent step from a special-fibre presentation. It does
not assert that a special fibre is a complete intersection.
-/

@[expose] public section

namespace Ideal

variable {S : Type*} [CommRing S]

/-- Generators modulo a radical element generate a finitely generated saturated ideal. -/
theorem eq_of_le_sup_span_singleton_of_saturated {J K : Ideal S} {p : S}
    (hK : K.FG) (hp : p ∈ jacobson (⊥ : Ideal S)) (hJK : J ≤ K)
    (hsat : ∀ x : S, p * x ∈ K → x ∈ K)
    (hgen : K ≤ J ⊔ span {p}) : J = K := by
  apply le_antisymm hJK
  apply Submodule.le_of_le_smul_of_le_jacobson_bot hK
    (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hp))
  intro x hx
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp (hgen hx)
  obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton.mp hz
  have hw : w ∈ K := hsat w ((K.add_mem_iff_right (hJK hy)).mp hx)
  exact Submodule.mem_sup.mpr ⟨y, hy, p * w,
    Submodule.smul_mem_smul (Ideal.mem_span_singleton_self p) hw, rfl⟩

/-- Equality of reduced ideals detects generators when the larger ideal is saturated. -/
theorem eq_of_map_quotient_span_singleton_eq_of_saturated {J K : Ideal S} {p : S}
    (hK : K.FG) (hp : p ∈ jacobson (⊥ : Ideal S)) (hJK : J ≤ K)
    (hsat : ∀ x : S, p * x ∈ K → x ∈ K)
    (hgen : J.map (Quotient.mk (span {p})) = K.map (Quotient.mk (span {p}))) :
    J = K := by
  apply eq_of_le_sup_span_singleton_of_saturated hK hp hJK hsat
  have h := congrArg (Ideal.comap (Quotient.mk (span {p}))) hgen
  simp only [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective] at h
  change J ⊔ RingHom.ker (Quotient.mk (span {p})) =
    K ⊔ RingHom.ker (Quotient.mk (span {p})) at h
  rw [Ideal.mk_ker] at h
  exact le_sup_left.trans h.ge

end Ideal

namespace AlgHom

variable {R S A : Type*} [CommRing R] [CommRing S] [CommRing A]
  [Algebra R S] [Algebra R A]

/-- Reduction of an algebra homomorphism modulo a principal ideal of the base. -/
def modPrincipal (f : S →ₐ[R] A) (p : R) :
    S ⧸ Ideal.span {algebraMap R S p} →ₐ[R] A ⧸ Ideal.span {algebraMap R A p} :=
  Ideal.quotientMapₐ _ f (Ideal.span_le.mpr <| Set.singleton_subset_iff.mpr <| by
    change f (algebraMap R S p) ∈ Ideal.span {algebraMap R A p}
    rw [f.commutes]
    exact Ideal.mem_span_singleton_self _)

/-- Reduction commutes with the quotient maps. -/
@[simp] theorem modPrincipal_mk (f : S →ₐ[R] A) (p : R) (x : S) :
    f.modPrincipal p (Ideal.Quotient.mk (Ideal.span {algebraMap R S p}) x) =
      Ideal.Quotient.mk (Ideal.span {algebraMap R A p}) (f x) := rfl

/-- Every special-fibre relation of a surjective algebra map lifts to an actual
relation, after correcting an arbitrary lift by a multiple of the parameter. -/
theorem ker_modPrincipal (f : S →ₐ[R] A) (hf : Function.Surjective f) (p : R) :
    RingHom.ker (f.modPrincipal p) =
      (RingHom.ker f).map (Ideal.Quotient.mk (Ideal.span {algebraMap R S p})) := by
  ext x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [RingHom.mem_ker, modPrincipal_mk, Ideal.Quotient.eq_zero_iff_mem]
  constructor
  · intro hx
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp hx
    obtain ⟨y, rfl⟩ := hf a
    apply (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mpr
    refine ⟨x - algebraMap R S p * y, ?_, ?_⟩
    · simp only [RingHom.mem_ker, map_sub, map_mul, f.commutes, ← ha, sub_self]
    · rw [map_sub, map_mul]
      have hp : Ideal.Quotient.mk (Ideal.span {algebraMap R S p})
          (algebraMap R S p) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
      rw [hp, zero_mul, sub_zero]
  · intro hx
    obtain ⟨y, hy, hxy⟩ :=
      (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp hx
    have hxy' : f.modPrincipal p (Ideal.Quotient.mk _ y) =
        f.modPrincipal p (Ideal.Quotient.mk _ x) := congrArg (f.modPrincipal p) hxy
    rw [modPrincipal_mk, modPrincipal_mk, show f y = 0 from hy, map_zero] at hxy'
    exact Ideal.Quotient.eq_zero_iff_mem.mp hxy'.symm

/-- Flatness makes the kernel of an algebra map saturated with respect to every
regular element of the base ring. -/
theorem mul_mem_ker_iff_of_flat [Module.Flat R A] (f : S →ₐ[R] A)
    {p : R} (hp : IsRegular p) (x : S) :
    algebraMap R S p * x ∈ RingHom.ker f ↔ x ∈ RingHom.ker f := by
  simp only [RingHom.mem_ker, map_mul, f.commutes]
  constructor
  · intro h
    apply Module.Flat.isSMulRegular_of_isRegular (M := A) hp
    simpa only [Algebra.smul_def, mul_zero] using h
  · intro h
    rw [h, mul_zero]

/-- Relations spanning the reduced kernel span the entire kernel of a map to a
flat algebra. The source may be a local polynomial ring or a power series ring. -/
theorem span_eq_ker_of_flat_of_span_quotient_eq [Module.Flat R A]
    (f : S →ₐ[R] A) (hker : (RingHom.ker f).FG)
    {p : R} (hp : IsRegular p)
    (hjac : algebraMap R S p ∈ Ideal.jacobson (⊥ : Ideal S))
    {ι : Type*} (g : ι → S) (hg : ∀ i, f (g i) = 0)
    (hgen : Ideal.span (Set.range (fun i ↦
        Ideal.Quotient.mk (Ideal.span {algebraMap R S p}) (g i))) =
      (RingHom.ker f).map (Ideal.Quotient.mk (Ideal.span {algebraMap R S p}))) :
    Ideal.span (Set.range g) = RingHom.ker f := by
  apply Ideal.eq_of_map_quotient_span_singleton_eq_of_saturated hker hjac
  · exact Ideal.span_le.mpr (Set.range_subset_iff.mpr hg)
  · intro x hx
    exact (f.mul_mem_ker_iff_of_flat hp x).mp hx
  · simpa only [Ideal.map_span, ← Set.range_comp, Function.comp_def] using hgen

/-- A generating family of special-fibre relations lifts, with the same index
set, to a family generating the whole kernel. No complete-intersection
assumption on the original algebra is used. -/
theorem exists_span_eq_ker_of_flat_of_modPrincipal [Module.Flat R A]
    (f : S →ₐ[R] A) (hf : Function.Surjective f) (hker : (RingHom.ker f).FG)
    {p : R} (hp : IsRegular p)
    (hjac : algebraMap R S p ∈ Ideal.jacobson (⊥ : Ideal S))
    {ι : Type*} (g₀ : ι → S ⧸ Ideal.span {algebraMap R S p})
    (hgen : Ideal.span (Set.range g₀) = RingHom.ker (f.modPrincipal p)) :
    ∃ g : ι → S,
      (∀ i, Ideal.Quotient.mk (Ideal.span {algebraMap R S p}) (g i) = g₀ i) ∧
      Ideal.span (Set.range g) = RingHom.ker f := by
  have hg₀ (i : ι) : g₀ i ∈
      (RingHom.ker f).map (Ideal.Quotient.mk (Ideal.span {algebraMap R S p})) := by
    rw [← f.ker_modPrincipal hf p, ← hgen]
    exact Ideal.subset_span ⟨i, rfl⟩
  classical
  choose g hg hred using fun i ↦
    (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp (hg₀ i)
  refine ⟨g, hred, f.span_eq_ker_of_flat_of_span_quotient_eq hker hp hjac g hg ?_⟩
  simpa only [hred, ← f.ker_modPrincipal hf p] using hgen

/-- A finite special-fibre presentation descends to an actual quotient
presentation with exactly the same number of relations. -/
theorem exists_quotient_equiv_of_flat_of_modPrincipal [Module.Flat R A]
    (f : S →ₐ[R] A) (hf : Function.Surjective f) (hker : (RingHom.ker f).FG)
    {p : R} (hp : IsRegular p)
    (hjac : algebraMap R S p ∈ Ideal.jacobson (⊥ : Ideal S))
    {n : ℕ} (g₀ : Fin n → S ⧸ Ideal.span {algebraMap R S p})
    (hgen : Ideal.span (Set.range g₀) = RingHom.ker (f.modPrincipal p)) :
    ∃ (g : Fin n → S) (e : (S ⧸ Ideal.span (Set.range g)) ≃ₐ[R] A),
      (∀ i, Ideal.Quotient.mk (Ideal.span {algebraMap R S p}) (g i) = g₀ i) ∧
      ∀ x, e (Ideal.Quotient.mk _ x) = f x := by
  obtain ⟨g, hg, hker'⟩ :=
    f.exists_span_eq_ker_of_flat_of_modPrincipal hf hker hp hjac g₀ hgen
  refine ⟨g, (Ideal.quotientEquivAlgOfEq R hker').trans
    (Ideal.quotientKerAlgEquivOfSurjective hf), hg, fun x ↦ ?_⟩
  rfl

end AlgHom
