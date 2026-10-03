/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.NormalLatticeExpDomain
public import FLT.LocalClassFieldTheory.IntegralNormalLatticeIntCohomology

/-!
# The exponential unit subgroup of the scaled normal lattice

Apply the actual exponential to p² times the constructed normal lattice.
Its injective homomorphism identifies the lattice with an actual subgroup
of field units; the natural Galois action preserves this subgroup.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open IsLocalRing

variable (R S K L : Type)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Algebra R S] [Module.Finite R S]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field L] [Algebra S L] [IsFractionRing S L] [Algebra K L] [Algebra R L]
  [IsScalarTower R K L] [IsScalarTower R S L]
  [FiniteDimensional K L] [IsGalois K L] [CharZero L]
  [IsAdicComplete (maximalIdeal S) S]
  (p : ℕ) [Fact p.Prime] [CharP (ResidueField S) p]

/-- Exponentiation of p² times the normal lattice, as an actual unit homomorphism. -/
def normalLatticeExpHom : Multiplicative (integralNormalLattice R K L) →* Lˣ :=
  (localExpHom S L p).comp (scaledNormalLatticeMap R S K L p).toMultiplicative

/-- The normal-lattice exponential loses no information. -/
theorem normalLatticeExpHom_injective : Function.Injective (normalLatticeExpHom R S K L p) := by
  intro x y h
  have h' := localExpHom_injective S L p h
  exact scaledNormalLatticeMap_injective R S K L p h'

/-- The concrete unit subgroup used to transport normal-lattice acyclicity. -/
def normalLatticeExpUnits : Subgroup Lˣ := (normalLatticeExpHom R S K L p).range

/-- The original additive normal lattice is equivalent to the unit subgroup. -/
def normalLatticeExpEquiv :
    Multiplicative (integralNormalLattice R K L) ≃* normalLatticeExpUnits R S K L p :=
  MonoidHom.ofInjective (normalLatticeExpHom_injective R S K L p)

/-- Exponentiation of the scaled lattice commutes with the actual Galois action. -/
theorem normalLatticeExpHom_galois (g : Gal(L/K)) (x : integralNormalLattice R K L) :
    normalLatticeExpHom R S K L p
      (Multiplicative.ofAdd (integralNormalLatticeRepresentation R K L g x)) =
      Units.map g.toMonoidHom (normalLatticeExpHom R S K L p (Multiplicative.ofAdd x)) := by
  let : Module.IsTorsionFree R L := .trans_faithfulSMul R K L
  let : IsIntegralClosure S R L := IsIntegralClosure.of_isIntegrallyClosed S R L
  apply Units.ext
  change adicLocalExp S L ((p : L) ^ 2 * g x.val) =
    g (adicLocalExp S L ((p : L) ^ 2 * x.val))
  simpa only [AlgEquiv.restrictScalars_apply, map_mul, map_pow, map_natCast] using
    (adicLocalExp_galois R S L p (g.restrictScalars R) _
      (scaledNormalLattice_mem_domain R S K L p x)).symm

/-- The natural Galois action preserves the constructed exponential subgroup. -/
theorem normalLatticeExpUnits_galois (g : Gal(L/K)) (u : normalLatticeExpUnits R S K L p) :
    Units.map g.toMonoidHom u.val ∈ normalLatticeExpUnits R S K L p := by
  obtain ⟨x, hx⟩ := u.property
  refine ⟨Multiplicative.ofAdd
    (integralNormalLatticeRepresentation R K L g (Multiplicative.toAdd x)), ?_⟩
  rw [normalLatticeExpHom_galois]
  change Units.map g.toMonoidHom (normalLatticeExpHom R S K L p x) = _
  rw [hx]

end LocalClassFieldTheory
