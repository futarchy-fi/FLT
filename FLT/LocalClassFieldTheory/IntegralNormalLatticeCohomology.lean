/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.IntegralNormalLatticeAction
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Shapiro

/-!
# Acyclicity of the additive normal lattice

The proved coinduced comparison and Shapiro's lemma identify lattice
cohomology with that of the trivial subgroup. Every positive degree vanishes.
This concerns the additive lattice; no exponential or unit subgroup is used.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open CategoryTheory Limits

variable (R K L : Type) [CommRing R] [IsDomain R] [Field K] [Field L]
  [Algebra R K] [IsFractionRing R K] [Algebra K L] [Algebra R L]
  [IsScalarTower R K L] [FiniteDimensional K L] [IsGalois K L]

/-- Shapiro's comparison for the constructed additive normal lattice. -/
def integralNormalLatticeCohomologyIso (i : ℕ) :
    groupCohomology (Rep.of (integralNormalLatticeRepresentation R K L)) i ≅
      groupCohomology (Rep.trivial R (⊥ : Subgroup Gal(L/K)) R) i :=
  groupCohomology.mapIso (MulEquiv.refl Gal(L/K)) (integralNormalLatticeCoindEquiv R K L)
    (fun g => by
      apply LinearMap.ext
      exact integralNormalLatticeCoindEquiv_action R K L g) i ≪≫
    groupCohomology.coindIso (Rep.trivial R (⊥ : Subgroup Gal(L/K)) R) i

/-- The actual additive normal lattice has vanishing positive R-linear group cohomology. -/
theorem integralNormalLattice_cohomology_isZero (i : ℕ) :
    IsZero (groupCohomology (Rep.of (integralNormalLatticeRepresentation R K L)) (i + 1)) :=
  (isZero_groupCohomology_succ_of_subsingleton
    (Rep.trivial R (⊥ : Subgroup Gal(L/K)) R) i).of_iso
      (integralNormalLatticeCohomologyIso R K L (i + 1))

end LocalClassFieldTheory
