/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.ResidueGaloisEquiv
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Arithmetic Frobenius in an unramified DVR extension

Frobenius is constructed by inverting the proved residue Galois equivalence.
It acts by the cardinality of the base residue field, and its powers exhaust
the Galois group. This fixes the arithmetic, rather than geometric, convention.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open IsLocalRing

variable (R S K L : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Field K] [Field L] [Algebra R K] [IsFractionRing R K]
  [Algebra S L] [IsFractionRing S L] [Algebra R S] [Algebra K L] [Algebra R L]
  [IsScalarTower R K L] [IsScalarTower R S L] [IsIntegralClosure S R L]
  [FiniteDimensional K L] [IsGalois K L] [IsLocalHom (algebraMap R S)]
  [Algebra.FormallyUnramified R S] [Finite (ResidueField R)]

/-- The arithmetic Frobenius of an unramified integral DVR extension. -/
def arithmeticFrobenius : Gal(L/K) :=
  letI := Fintype.ofFinite (ResidueField R)
  letI := IsIntegralClosure.finite R K L S
  (residueGaloisEquiv R S K L).symm
    (FiniteField.frobeniusAlgEquivOfAlgebraic (ResidueField R) (ResidueField S))

/-- Reduction of arithmetic Frobenius is the qth-power map. -/
theorem arithmeticFrobenius_residue (x : ResidueField S) :
    residueGaloisAction R S K L (arithmeticFrobenius R S K L) x =
      x ^ Nat.card (ResidueField R) := by
  let := Fintype.ofFinite (ResidueField R)
  let := IsIntegralClosure.finite R K L S
  change residueGaloisEquiv R S K L ((residueGaloisEquiv R S K L).symm _) x = _
  rw [MulEquiv.apply_symm_apply]
  simp [Nat.card_eq_fintype_card]

/-- The qth-power rule holds on representatives in the ring of integers. -/
theorem arithmeticFrobenius_residue_integral (x : S) :
    residue S (galRestrict R K L S (arithmeticFrobenius R S K L) x) =
      residue S x ^ Nat.card (ResidueField R) :=
  arithmeticFrobenius_residue R S K L (residue S x)

/-- The residue qth-power rule uniquely determines Frobenius. -/
theorem arithmeticFrobenius_unique (σ : Gal(L/K))
    (hσ : ∀ x : S, residue S (galRestrict R K L S σ x) =
      residue S x ^ Nat.card (ResidueField R)) : σ = arithmeticFrobenius R S K L := by
  apply residueGaloisAction_injective R S K L
  ext x
  obtain ⟨x, rfl⟩ := residue_surjective x
  exact (hσ x).trans (arithmeticFrobenius_residue_integral R S K L x).symm

/-- Frobenius has order equal to the residue extension degree. -/
theorem orderOf_arithmeticFrobenius :
    orderOf (arithmeticFrobenius R S K L) =
      Module.finrank (ResidueField R) (ResidueField S) := by
  let := Fintype.ofFinite (ResidueField R)
  let := IsIntegralClosure.finite R K L S
  let := ResidueField.finite_of_finite (R := R) (S := S) inferInstance
  exact ((residueGaloisEquiv R S K L).symm.orderOf_eq _).trans
    (FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic (ResidueField R) (ResidueField S))

/-- Every field automorphism is a power of arithmetic Frobenius, with exponent
strictly less than the residue extension degree. -/
theorem arithmeticFrobenius_pow_surjective :
    Function.Surjective (fun i : Fin (Module.finrank (ResidueField R) (ResidueField S)) =>
      arithmeticFrobenius R S K L ^ i.val) := by
  let := Fintype.ofFinite (ResidueField R)
  let := IsIntegralClosure.finite R K L S
  let := ResidueField.finite_of_finite (R := R) (S := S) inferInstance
  intro σ
  obtain ⟨i, hi⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow
    (ResidueField R) (ResidueField S)).surjective (residueGaloisEquiv R S K L σ)
  refine ⟨i, ?_⟩
  simpa only [arithmeticFrobenius, map_pow, MulEquiv.symm_apply_apply] using
    congrArg (residueGaloisEquiv R S K L).symm hi

end LocalClassFieldTheory
