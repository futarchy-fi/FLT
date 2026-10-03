/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.NormalLatticeExpUnits
public import FLT.LocalClassFieldTheory.LocalExpOpen

/-!
# Openness of the exponential normal-lattice subgroup

The scalar image p²Λ is open in the actual fraction field. Its image
under the proved open exponential map is precisely the constructed unit
subgroup, so that subgroup is open as well.
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

/-- The constructed normal-lattice exponential is an open subgroup of field units. -/
theorem normalLatticeExpUnits_isOpen :
    letI := dvrAdicValued S L
    IsOpen (normalLatticeExpUnits R S K L p : Set Lˣ) := by
  let := dvrAdicValued S L
  have hr : Set.range (scaledNormalLatticeMap R S K L p).toMultiplicative =
      (fun x : Multiplicative (localExpDomain S L p) => (Multiplicative.toAdd x).val) ⁻¹'
        ((fun x : L => (p : L) ^ 2 * x) '' (integralNormalLattice R K L : Set L)) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨(Multiplicative.toAdd x).val, (Multiplicative.toAdd x).property, rfl⟩
    · rintro ⟨x, hx, hxy⟩
      refine ⟨Multiplicative.ofAdd ⟨x, hx⟩, ?_⟩
      exact Subtype.ext hxy
  have hopen : IsOpen (Set.range (scaledNormalLatticeMap R S K L p).toMultiplicative) := by
    rw [hr]
    exact (scaledNormalLattice_isOpen R S K L p).preimage
      (continuous_subtype_val.comp continuous_toAdd)
  change IsOpen (Set.range ((localExpHom S L p) ∘
    (scaledNormalLatticeMap R S K L p).toMultiplicative))
  rw [Set.range_comp]
  exact localExpHom_isOpenMap S L p _ hopen

end LocalClassFieldTheory
