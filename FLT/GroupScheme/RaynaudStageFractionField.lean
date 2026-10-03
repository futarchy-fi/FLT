/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudUnramifiedStage
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.LocalRing.Quotient

/-!
# Fraction fields of embedded finite DVR stages

The fraction field of an embedded finite stage acquires its compatible base-field
algebra and embeds in the same closure. Over a perfect base field this is a finite
separable extension. Its degree is the integral module rank.
-/

@[expose] public noncomputable section

namespace RaynaudParameters

variable {R K S Ω : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [PerfectField K] [Algebra R K] [IsFractionRing R K]
  [CommRing S] [IsDomain S] [Algebra R S] [Module.Finite R S]
  [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower R K Ω]

/-- Construct the finite separable fraction field and the compatible embedding
from the finite integral stage; neither field algebra nor embedding is an input. -/
theorem exists_stage_fraction_field (f : S →ₐ[R] Ω) (hf : Function.Injective f) :
    ∃ (_ : Algebra K (FractionRing S)) (_ : IsScalarTower R K (FractionRing S))
      (_ : FiniteDimensional K (FractionRing S)) (_ : Algebra.IsSeparable K (FractionRing S))
      (e : FractionRing S →ₐ[K] Ω),
      (∀ s : S, e (algebraMap S (FractionRing S) s) = f s) ∧
      Module.finrank K (FractionRing S) = Module.finrank R S := by
  have hR : Function.Injective (algebraMap R S) := by
    intro x y h
    apply algebraMap_injective_of_field_isFractionRing R Ω K Ω
    simpa only [f.commutes] using congrArg f h
  let : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).mpr hR
  let L := FractionRing S
  have hinj : Function.Injective (algebraMap R L) :=
    (IsFractionRing.injective S L).comp hR
  let algKL : Algebra K L := (IsFractionRing.lift hinj : K →+* L).toAlgebra
  let tower : IsScalarTower R K L := IsScalarTower.of_algebraMap_eq fun r ↦
    (IsFractionRing.lift_algebraMap hinj r).symm
  have hrank : Module.finrank K L = Module.finrank R S := IsFractionRing.finrank_eq R K S L
  let finite : FiniteDimensional K L := Module.finite_of_finrank_pos
    (hrank ▸ Module.finrank_pos)
  let eR : L →ₐ[R] Ω := IsFractionRing.liftAlgHom hf
  have hcomm : eR.toRingHom.comp (algebraMap K L) = algebraMap K Ω := by
    apply IsFractionRing.ringHom_ext (A := R)
    intro r
    simp only [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply R K L,
      ← IsScalarTower.algebraMap_apply R K Ω]
    exact eR.commutes r
  let e : L →ₐ[K] Ω := { eR.toRingHom with commutes' := RingHom.congr_fun hcomm }
  exact ⟨algKL, tower, finite, inferInstance, e,
    fun s ↦ IsFractionRing.lift_algebraMap hf s, hrank⟩

omit [IsDomain R] [IsDiscreteValuationRing R] [PerfectField K] [IsFractionRing R K]
  [Module.Finite R S] [Algebra R Ω] [IsScalarTower R K Ω] in
/-- The fraction-field embedding is uniquely determined by the given stage map. -/
theorem stage_fraction_field_embedding_unique
    [Algebra K (FractionRing S)]
    {e₁ e₂ : FractionRing S →ₐ[K] Ω}
    (h : ∀ s : S, e₁ (algebraMap S (FractionRing S) s) =
      e₂ (algebraMap S (FractionRing S) s)) : e₁ = e₂ :=
  AlgHom.coe_ringHom_injective (IsFractionRing.ringHom_ext h)

omit [PerfectField K] [Algebra R Ω] [IsScalarTower R K Ω] in
/-- A finite stage with unchanged uniformizer has field degree equal to residue degree. -/
theorem stage_fraction_field_degree [IsLocalRing S] [IsLocalHom (algebraMap R S)]
    [FaithfulSMul R S] [Algebra K (FractionRing S)] [IsScalarTower R K (FractionRing S)]
    (hm : (IsLocalRing.maximalIdeal R).map (algebraMap R S) = IsLocalRing.maximalIdeal S) :
    Module.finrank K (FractionRing S) =
      Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) := by
  let e := AddEquiv.toLinearEquiv (R := R ⧸ IsLocalRing.maximalIdeal R)
    (Ideal.quotEquivOfEq hm).toAddEquiv (fun r x ↦ by
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      rfl)
  rw [IsFractionRing.finrank_eq R K S (FractionRing S),
    ← IsLocalRing.finrank_quotient_map (R := R) (S := S)]
  exact e.finrank_eq

end RaynaudParameters
