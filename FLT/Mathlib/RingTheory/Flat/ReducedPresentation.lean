/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.RingTheory.Flat.FibreRelationLifting

/-! # Actual reduction of a presentation modulo an arbitrary base ideal -/

@[expose] public noncomputable section

namespace AlgHom

variable {R S A : Type*} [CommRing R] [CommRing S] [CommRing A]
  [Algebra R S] [Algebra R A]

/-- The extended base ideal commutes with an algebra presentation map. -/
theorem map_extended_base_ideal (f : S →ₐ[R] A) (J : Ideal R) :
    (J.map (algebraMap R S)).map f.toRingHom = J.map (algebraMap R A) := by
  rw [Ideal.map_map]
  congr 1
  exact f.comp_algebraMap

/-- Reduce the specified presentation modulo a base ideal. -/
def modBaseIdeal (f : S →ₐ[R] A) (J : Ideal R) :
    (S ⧸ J.map (algebraMap R S)) →ₐ[R] (A ⧸ J.map (algebraMap R A)) :=
  Ideal.quotientMapₐ _ f (by
    apply Ideal.map_le_iff_le_comap.mp
    exact (f.map_extended_base_ideal J).le)

@[simp] theorem modBaseIdeal_mk (f : S →ₐ[R] A) (J : Ideal R) (s : S) :
    f.modBaseIdeal J (Ideal.Quotient.mk _ s) = Ideal.Quotient.mk _ (f s) := rfl

/-- No extra relations occur in the reduced presentation kernel. -/
theorem ker_modBaseIdeal (f : S →ₐ[R] A) (hf : Function.Surjective f) (J : Ideal R) :
    RingHom.ker (f.modBaseIdeal J) =
      (RingHom.ker f).map (Ideal.Quotient.mk (J.map (algebraMap R S))) := by
  apply Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective
  have hc : (RingHom.ker (f.modBaseIdeal J)).comap
      (Ideal.Quotient.mk (J.map (algebraMap R S))) =
      (J.map (algebraMap R A)).comap f.toRingHom := by
    ext s
    change Ideal.Quotient.mk _ (f s) = 0 ↔ f s ∈ J.map (algebraMap R A)
    exact Ideal.Quotient.eq_zero_iff_mem
  rw [hc, ← f.map_extended_base_ideal J,
    Ideal.comap_map_of_surjective f.toRingHom hf,
    Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective]
  change J.map (algebraMap R S) ⊔ RingHom.ker f =
    RingHom.ker f ⊔ RingHom.ker (Ideal.Quotient.mk (J.map (algebraMap R S)))
  rw [Ideal.mk_ker, sup_comm]

/-- Lift generators of the actual reduced kernel and retain the original quotient map.
Flatness and Nakayama prove that the lifted relations generate the whole kernel. -/
theorem exists_presentation_of_flat_modBaseIdeal [Module.Flat R A]
    (f : S →ₐ[R] A) (hf : Function.Surjective f) (hker : (RingHom.ker f).FG)
    (J : Ideal R) (hJ : J.map (algebraMap R S) ≤ Ideal.jacobson (⊥ : Ideal S))
    {n : ℕ} (v : Fin n → S ⧸ J.map (algebraMap R S))
    (hv : Ideal.span (Set.range v) = RingHom.ker (f.modBaseIdeal J)) :
    ∃ (w : Fin n → S) (e : (S ⧸ Ideal.span (Set.range w)) ≃ₐ[R] A),
      (∀ i, Ideal.Quotient.mk (J.map (algebraMap R S)) (w i) = v i) ∧
      ∀ s, e (Ideal.Quotient.mk _ s) = f s := by
  rw [f.ker_modBaseIdeal hf J] at hv
  obtain ⟨w, hw, hgen⟩ := f.exists_kernel_generators_of_flat_quotient hf hker J hJ v hv
  exact ⟨w, (Ideal.quotientEquivAlgOfEq R hgen).trans
    (Ideal.quotientKerAlgEquivOfSurjective hf), hw, fun _ ↦ rfl⟩

end AlgHom
