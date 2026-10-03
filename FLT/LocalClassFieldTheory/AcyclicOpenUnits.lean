/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.NormalLatticeExpOpen

/-!
# An actual acyclic open subgroup of local units

The exponential identifies p² times the constructed normal lattice with
an open subgroup of field units. Transport its proved integral cohomology
vanishing, and verify that the transported action is exactly the natural
Galois action on unit values.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open IsLocalRing CategoryTheory Limits

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

/-- The exponential lattice comparison as an integral linear equivalence. -/
def normalLatticeExpLinearEquiv : integralNormalLattice R K L ≃ₗ[ℤ]
    Additive (normalLatticeExpUnits R S K L p) :=
  (normalLatticeExpEquiv R S K L p).toAdditiveRight.toIntLinearEquiv

/-- The integral representation transported to the actual open unit subgroup. -/
def normalLatticeExpRepresentation :
    Representation ℤ Gal(L/K) (Additive (normalLatticeExpUnits R S K L p)) :=
  (normalLatticeExpLinearEquiv R S K L p).conjRingEquiv.toMonoidHom.comp
    (integralNormalLatticeIntRepresentation R K L)

/-- Transported action is exactly the natural Galois action on unit values. -/
theorem normalLatticeExpRepresentation_action (g : Gal(L/K))
    (u : Additive (normalLatticeExpUnits R S K L p)) :
    (Additive.toMul (normalLatticeExpRepresentation R S K L p g u)).val =
      Units.map g.toMonoidHom (Additive.toMul u).val := by
  obtain ⟨x, rfl⟩ := (normalLatticeExpLinearEquiv R S K L p).surjective u
  change (Additive.toMul (normalLatticeExpLinearEquiv R S K L p
    (integralNormalLatticeIntRepresentation R K L g
      ((normalLatticeExpLinearEquiv R S K L p).symm
        (normalLatticeExpLinearEquiv R S K L p x))))).val = _
  rw [LinearEquiv.symm_apply_apply]
  exact normalLatticeExpHom_galois R S K L p g x

/-- The exponential comparison intertwines the integral representations. -/
theorem normalLatticeExpLinearEquiv_action (g : Gal(L/K)) (x : integralNormalLattice R K L) :
    normalLatticeExpLinearEquiv R S K L p (integralNormalLatticeIntRepresentation R K L g x) =
      normalLatticeExpRepresentation R S K L p g (normalLatticeExpLinearEquiv R S K L p x) := by
  change _ = normalLatticeExpLinearEquiv R S K L p
    (integralNormalLatticeIntRepresentation R K L g
      ((normalLatticeExpLinearEquiv R S K L p).symm
        (normalLatticeExpLinearEquiv R S K L p x)))
  rw [LinearEquiv.symm_apply_apply]

/-- Cohomology of the actual open unit subgroup agrees with normal-lattice cohomology. -/
def normalLatticeExpCohomologyIso (i : ℕ) :
    groupCohomology (Rep.of (integralNormalLatticeIntRepresentation R K L)) i ≅
      groupCohomology (Rep.of (normalLatticeExpRepresentation R S K L p)) i :=
  groupCohomology.mapIso (MulEquiv.refl Gal(L/K)) (normalLatticeExpLinearEquiv R S K L p)
    (fun g => by
      apply LinearMap.ext
      exact normalLatticeExpLinearEquiv_action R S K L p g) i

/-- Every positive integral cohomology group of the constructed open units vanishes. -/
theorem normalLatticeExpUnits_cohomology_isZero (i : ℕ) :
    IsZero (groupCohomology (Rep.of (normalLatticeExpRepresentation R S K L p)) (i + 1)) :=
  (integralNormalLattice_intCohomology_isZero R K L i).of_iso
    (normalLatticeExpCohomologyIso R S K L p (i + 1)).symm

end LocalClassFieldTheory
