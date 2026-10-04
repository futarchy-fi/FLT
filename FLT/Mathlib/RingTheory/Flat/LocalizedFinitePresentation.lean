/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.RingTheory.Flat.ReducedPresentation
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Localization.Algebra
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Flat.Localization

/-! # Finite kernels and radical base ideals in localized presentations -/

@[expose] public noncomputable section

namespace AlgHom

variable {R S A : Type*} [CommRing R] [CommRing S] [CommRing A]
  [Algebra R S] [Algebra R A]

/-- Localize a specified presentation at a prime of its target. -/
def presentationAtPrime (f : S →ₐ[R] A) (Q : Ideal A) [Q.IsPrime] :
    Localization.AtPrime (Q.comap (f : S →+* A)) →ₐ[R] Localization.AtPrime Q where
  __ := Localization.localRingHom _ Q (f : S →+* A) rfl
  commutes' r := by
    change Localization.localRingHom _ Q (f : S →+* A) rfl (algebraMap R _ r) = _
    rw [IsScalarTower.algebraMap_apply R S, Localization.localRingHom_to_map]
    change algebraMap A _ (f (algebraMap R S r)) = _
    rw [f.commutes, ← IsScalarTower.algebraMap_apply R A]

@[simp] theorem presentationAtPrime_algebraMap (f : S →ₐ[R] A)
    (Q : Ideal A) [Q.IsPrime] (s : S) :
    f.presentationAtPrime Q (algebraMap S _ s) = algebraMap A _ (f s) :=
  Localization.localRingHom_to_map _ _ _ rfl _

/-- A surjection identifies the two sets of denominators exactly. -/
theorem map_primeCompl_comap_of_surjective (f : S →ₐ[R] A)
    (hf : Function.Surjective f) (Q : Ideal A) [Q.IsPrime] :
    (Q.comap (f : S →+* A)).primeCompl.map (f : S →+* A) = Q.primeCompl := by
  ext a
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact hs
  · intro ha
    obtain ⟨s, rfl⟩ := hf a
    exact ⟨s, ha, rfl⟩

/-- The actual local presentation remains surjective. -/
theorem presentationAtPrime_surjective (f : S →ₐ[R] A)
    (hf : Function.Surjective f) (Q : Ideal A) [Q.IsPrime] :
    Function.Surjective (f.presentationAtPrime Q) := by
  have h := f.map_primeCompl_comap_of_surjective hf Q
  let : IsLocalization ((Q.comap (f : S →+* A)).primeCompl.map (f : S →+* A))
      (Localization.AtPrime Q) := h.symm ▸ inferInstance
  exact IsLocalization.map_surjective_of_surjective (g := (f : S →+* A))
    (Q.comap (f : S →+* A)).primeCompl
    (Localization.AtPrime (Q.comap (f : S →+* A))) (Localization.AtPrime Q) hf

/-- Localization preserves the whole kernel, including its finite generation. -/
theorem ker_presentationAtPrime (f : S →ₐ[R] A)
    (hf : Function.Surjective f) (Q : Ideal A) [Q.IsPrime] :
    RingHom.ker (f.presentationAtPrime Q) =
      (RingHom.ker f).map (algebraMap S (Localization.AtPrime (Q.comap (f : S →+* A)))) :=
  IsLocalization.ker_map _ (f : S →+* A) (f.map_primeCompl_comap_of_surjective hf Q)

/-- Finite presentation supplies the finite localized kernel over an arbitrary base. -/
theorem ker_presentationAtPrime_fg [Algebra.FinitePresentation R S]
    [Algebra.FinitePresentation R A] (f : S →ₐ[R] A)
    (hf : Function.Surjective f) (Q : Ideal A) [Q.IsPrime] :
    (RingHom.ker (f.presentationAtPrime Q)).FG := by
  rw [f.ker_presentationAtPrime hf Q]
  exact (Algebra.FinitePresentation.ker_fG_of_surjective f hf).map _

/-- The contraction of the target prime extends into the localized source's radical. -/
theorem baseIdeal_le_jacobson_presentationAtPrime (f : S →ₐ[R] A)
    (Q : Ideal A) [Q.IsPrime] :
    (Q.comap (algebraMap R A)).map
        (algebraMap R (Localization.AtPrime (Q.comap (f : S →+* A)))) ≤
      Ideal.jacobson (⊥ : Ideal (Localization.AtPrime (Q.comap (f : S →+* A)))) := by
  rw [IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top]
  apply Ideal.map_le_iff_le_comap.mpr
  intro r hr
  rw [Ideal.mem_comap, IsScalarTower.algebraMap_apply R S,
    IsLocalization.AtPrime.to_map_mem_maximal_iff
      (Localization.AtPrime (Q.comap (f : S →+* A))) (Q.comap (f : S →+* A))]
  change f (algebraMap R S r) ∈ Q
  rw [f.commutes]
  exact hr

end AlgHom
