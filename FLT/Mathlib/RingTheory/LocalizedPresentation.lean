/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.RingTheory.RelationLifting
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.Localization.Submodule

/-!
# Localizing a presentation at the target's maximal ideal

A surjection onto a local algebra extends to the source localized at the
preimage of the maximal ideal. Its kernel is the extension of the original
kernel, and the resulting source is local, so radical parameters can be
used in relation lifting.
-/

@[expose] public noncomputable section

namespace AlgHom

variable {R S A : Type*} [CommRing R] [CommRing S] [CommRing A]
  [Algebra R S] [Algebra R A] [IsLocalRing A]

/-- The source localized at the inverse image of the target's maximal ideal. -/
abbrev localizedSource (f : S →ₐ[R] A) :=
  Localization.AtPrime ((IsLocalRing.maximalIdeal A).comap (f : S →+* A))

/-- Extend an algebra map to the source localized at the inverse image of
the target's maximal ideal. -/
def localizeAtMaximal (f : S →ₐ[R] A) :
    Localization.AtPrime ((IsLocalRing.maximalIdeal A).comap (f : S →+* A)) →ₐ[R] A :=
  IsLocalization.liftAlgHom (f := f)
    (M := ((IsLocalRing.maximalIdeal A).comap (f : S →+* A)).primeCompl)
    fun s ↦ IsLocalRing.notMem_maximalIdeal.mp s.property

/-- The localized map agrees with the original map on the original source. -/
@[simp] theorem localizeAtMaximal_algebraMap (f : S →ₐ[R] A) (s : S) :
    f.localizeAtMaximal
      (algebraMap S (Localization.AtPrime
        ((IsLocalRing.maximalIdeal A).comap (f : S →+* A))) s) = f s :=
  IsLocalization.lift_eq _ s

/-- Localization preserves surjectivity of a presentation of a local algebra. -/
theorem localizeAtMaximal_surjective (f : S →ₐ[R] A) (hf : Function.Surjective f) :
    Function.Surjective f.localizeAtMaximal := by
  intro a
  obtain ⟨s, rfl⟩ := hf a
  exact ⟨algebraMap S _ s, f.localizeAtMaximal_algebraMap s⟩

/-- The localized kernel is precisely the extension of the original kernel. -/
theorem ker_localizeAtMaximal (f : S →ₐ[R] A) :
    RingHom.ker f.localizeAtMaximal =
      (RingHom.ker f).map (algebraMap S (Localization.AtPrime
        ((IsLocalRing.maximalIdeal A).comap (f : S →+* A)))) := by
  let P := (IsLocalRing.maximalIdeal A).comap (f : S →+* A)
  let L := Localization.AtPrime P
  have hc : (RingHom.ker f.localizeAtMaximal).comap (algebraMap S L) =
      RingHom.ker f := by
    ext s
    change f.localizeAtMaximal (algebraMap S L s) = 0 ↔ f s = 0
    rw [localizeAtMaximal_algebraMap]
  rw [← hc]
  exact (IsLocalization.map_under P.primeCompl L (RingHom.ker f.localizeAtMaximal)).symm

/-- A relation family generating the original kernel generates its localization. -/
theorem ker_localizeAtMaximal_eq_span (f : S →ₐ[R] A) {ι : Type*} (r : ι → S)
    (hr : RingHom.ker f = Ideal.span (Set.range r)) :
    RingHom.ker f.localizeAtMaximal =
      Ideal.span (Set.range (fun i ↦ algebraMap S (Localization.AtPrime
        ((IsLocalRing.maximalIdeal A).comap (f : S →+* A))) (r i))) := by
  rw [ker_localizeAtMaximal, hr, Ideal.map_span, ← Set.range_comp]
  rfl

/-- A base parameter in the target maximal ideal belongs to the Jacobson
radical of the localized presentation source. -/
theorem algebraMap_mem_jacobson_localizedSource (f : S →ₐ[R] A) (p : R)
    (hp : algebraMap R A p ∈ IsLocalRing.maximalIdeal A) :
    algebraMap R f.localizedSource p ∈ Ideal.jacobson (⊥ : Ideal f.localizedSource) := by
  rw [IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top,
    IsScalarTower.algebraMap_apply R S f.localizedSource]
  apply (IsLocalization.AtPrime.to_map_mem_maximal_iff f.localizedSource
    ((IsLocalRing.maximalIdeal A).comap (f : S →+* A)) (algebraMap R S p)).mpr
  change f (algebraMap R S p) ∈ IsLocalRing.maximalIdeal A
  rwa [f.commutes]

/-- Localizing a noetherian presentation supplies the radical and finite
kernel hypotheses needed to lift a square special-fibre presentation. -/
theorem exists_localized_quotient_equiv_of_flat_of_modPrincipal
    [IsNoetherianRing S] [Module.Flat R A]
    (f : S →ₐ[R] A) (hf : Function.Surjective f) {p : R} (hp : IsRegular p)
    (hpA : algebraMap R A p ∈ IsLocalRing.maximalIdeal A) {n : ℕ}
    (g₀ : Fin n → f.localizedSource ⧸
      Ideal.span {algebraMap R f.localizedSource p})
    (hgen : Ideal.span (Set.range g₀) = RingHom.ker (f.localizeAtMaximal.modPrincipal p)) :
    ∃ (g : Fin n → f.localizedSource)
        (e : (f.localizedSource ⧸ Ideal.span (Set.range g)) ≃ₐ[R] A),
      (∀ i, Ideal.Quotient.mk (Ideal.span {algebraMap R f.localizedSource p}) (g i) = g₀ i) ∧
      ∀ s, e (Ideal.Quotient.mk _ s) = f.localizeAtMaximal s := by
  exact f.localizeAtMaximal.exists_quotient_equiv_of_flat_of_modPrincipal
    (f.localizeAtMaximal_surjective hf) (IsNoetherian.noetherian _)
    hp (f.algebraMap_mem_jacobson_localizedSource p hpA) g₀ hgen

end AlgHom
