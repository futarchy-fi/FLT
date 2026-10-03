/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.IntegralNormalLatticeCohomology

/-!
# Integral cohomology of the additive normal lattice

Restricting scalars in the explicit coinduced equivalence gives the
vanishing theorem over Z required by multiplicative Galois cohomology.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open CategoryTheory Limits

variable (R K L : Type) [CommRing R] [IsDomain R] [Field K] [Field L]
  [Algebra R K] [IsFractionRing R K] [Algebra K L] [Algebra R L]
  [IsScalarTower R K L] [FiniteDimensional K L] [IsGalois K L]

/-- The same Galois action, regarded as an integral representation. -/
def integralNormalLatticeIntRepresentation :
    Representation ℤ Gal(L/K) (integralNormalLattice R K L) where
  toFun g := (integralNormalLatticeRepresentation R K L g).restrictScalars ℤ
  map_one' := by ext x; rfl
  map_mul' _ _ := by ext x; rfl

/-- The same inverse-indexed functions give the integral coinduced equivalence. -/
def integralNormalLatticeIntCoindEquiv : integralNormalLattice R K L ≃ₗ[ℤ]
    Representation.coindV (⊥ : Subgroup Gal(L/K)).subtype
      (Representation.trivial ℤ (⊥ : Subgroup Gal(L/K)) R) :=
  (integralNormalLatticeCoindEquiv R K L).restrictScalars ℤ

/-- Integral lattice cohomology is the cohomology of the trivial subgroup. -/
def integralNormalLatticeIntCohomologyIso (i : ℕ) :
    groupCohomology (Rep.of (integralNormalLatticeIntRepresentation R K L)) i ≅
      groupCohomology (Rep.trivial ℤ (⊥ : Subgroup Gal(L/K)) R) i :=
  groupCohomology.mapIso (MulEquiv.refl Gal(L/K)) (integralNormalLatticeIntCoindEquiv R K L)
    (fun g => by
      apply LinearMap.ext
      exact integralNormalLatticeCoindEquiv_action R K L g) i ≪≫
    groupCohomology.coindIso (Rep.trivial ℤ (⊥ : Subgroup Gal(L/K)) R) i

/-- Every positive integral cohomology group of the constructed additive lattice is zero. -/
theorem integralNormalLattice_intCohomology_isZero (i : ℕ) :
    IsZero (groupCohomology (Rep.of (integralNormalLatticeIntRepresentation R K L)) (i + 1)) :=
  (isZero_groupCohomology_succ_of_subsingleton
    (Rep.trivial ℤ (⊥ : Subgroup Gal(L/K)) R) i).of_iso
      (integralNormalLatticeIntCohomologyIso R K L (i + 1))

end LocalClassFieldTheory
