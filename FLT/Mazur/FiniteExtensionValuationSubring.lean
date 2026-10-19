/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.FiniteExtensionDVRModel
public import FLT.Mazur.ValuationRingModel

/-!
# Extending a discrete valuation subring to a prescribed finite extension

The constructed ring is Noetherian and discrete, has the prescribed fraction
field, and restricts to the exact original valuation subring.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.FiniteExtensionValuationSubring
open IsLocalRing
variable {K L : Type} [Field K] [Field L]

/-- A compatible local ring map proves equality with the restricted valuation ring. -/
theorem comap_eq (A : ValuationSubring K) (B : ValuationSubring L)
    (f : K →+* L) (φ : A →+* B) [IsLocalHom φ]
    (hφ : ∀ a : A, (φ a : L) = f a) : B.comap f = A := by
  ext x
  change f x ∈ B ↔ x ∈ A
  constructor
  · intro hx
    by_contra ha
    have hn : x ≠ 0 := fun h ↦ ha (h ▸ A.zero_mem)
    have hi := (A.mem_or_inv_mem x).resolve_left ha
    have hnu : (⟨x⁻¹, hi⟩ : A) ∈ maximalIdeal A :=
      A.coe_mem_nonunits_iff.mp (A.inv_mem_nonunits_iff.mpr (Or.inr ha))
    have hu : IsUnit (φ ⟨x⁻¹, hi⟩) := by
      apply IsUnit.of_mul_eq_one (⟨f x, hx⟩ : B)
      apply Subtype.ext
      change (φ ⟨x⁻¹, hi⟩ : L) * f x = 1
      rw [hφ, map_inv₀, inv_mul_cancel₀ ((map_ne_zero f).mpr hn)]
    exact hnu ((isUnit_map_iff φ _).mp hu)
  · intro hx
    have hm := (φ ⟨x, hx⟩).property
    rwa [hφ] at hm

variable [Algebra K L] [Module.Finite K L] [Algebra.IsSeparable K L]
  (A : ValuationSubring K) [IsDiscreteValuationRing A]

/-- Construct an extended Noetherian DVR inside the same finite separable extension field. -/
theorem exists_extension :
    ∃ (B : ValuationSubring L) (_ : IsDiscreteValuationRing B) (_ : IsNoetherianRing B)
      (φ : A →+* B), IsLocalHom φ ∧
      (∀ a : A, (φ a : L) = algebraMap K L a) ∧ B.comap (algebraMap K L) = A := by
  obtain ⟨S, hS, domS, dvrS, aS, aSL, tower, frac, hlocal⟩ :=
    FiniteExtensionDVRModel.exists_model A K L
  let _ := hS
  let _ := domS
  let _ := dvrS
  let _ := aS
  let _ := aSL
  let _ := tower
  let _ := frac
  let _ := hlocal
  let B := fractionValuationSubring S L
  let _ : IsDiscreteValuationRing B := fractionValuationSubring_isDiscreteValuationRing S L
  let φ : A →+* B := fractionValuationBaseMap
  have hφ (a : A) : (φ a : L) = algebraMap K L a :=
    fractionValuationBaseMap_coe a
  refine ⟨B, inferInstance, inferInstance, φ, inferInstance, hφ, ?_⟩
  exact comap_eq A B (algebraMap K L) φ hφ

end FLT.Mazur.FiniteExtensionValuationSubring
