/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.FiniteFlatClosureChange
public import FLT.GroupScheme.FiniteFlatSubquotientBaseChange
public import FLT.GroupScheme.RaynaudTowerAction

/-!
# Base change to a prescribed tower closure

Use the same original closure for integral base change, then the prescribed
closure equivalence. Conjugation retains the exact original automorphism.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace RaynaudParameters

variable {K L Ω : Type} [Field K] [Field L] [Field Ω]
  [Algebra K L] [Algebra K Ω] [IsAlgClosure K Ω]
  [Algebra L Ω] [IsScalarTower K L Ω]

/-- The tower equivalence as an algebra equivalence for the prescribed embedding. -/
def towerClosureAlgEquiv : AlgebraicClosure L ≃ₐ[L] Ω :=
  { towerClosureEquiv (IsScalarTower.toAlgHom K L Ω) with
    commutes' := towerClosureEquiv_algebraMap (IsScalarTower.toAlgHom K L Ω) }

/-- Conjugation of the original automorphism agrees with tower transport. -/
theorem towerClosureAlgEquiv_autCongr (σ : Ω ≃ₐ[K] Ω)
    (hσ : ∀ a : L, σ (algebraMap L Ω a) = algebraMap L Ω a) :
    AlgEquiv.autCongr (towerClosureAlgEquiv (K := K) (L := L) (Ω := Ω))
      (towerAutomorphism (IsScalarTower.toAlgHom K L Ω) σ hσ) =
      (show Ω ≃ₐ[L] Ω from { σ.toRingEquiv with commutes' := hσ }) := by
  ext x
  change towerClosureEquiv _
    (towerAutomorphism _ σ hσ ((towerClosureEquiv _).symm x)) = σ x
  rw [towerAutomorphism_apply, RingEquiv.apply_symm_apply]

end RaynaudParameters

namespace GaloisModule
open RaynaudParameters

variable {R S K L Ω X : Type} [CommRing R] [CommRing S] [Field K] [Field L] [Field Ω]
  [Algebra R K] [Algebra R S] [Algebra K L] [Algebra S L] [Algebra R L]
  [IsScalarTower R K L] [IsScalarTower R S L]
  [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω] [IsAlgClosure K Ω]
  [AddCommGroup X] [DistribMulAction (Ω ≃ₐ[K] Ω) X]

/-- The original point group on the prescribed tower closure. -/
abbrev TowerClosurePoints :=
  ClosureChangedPoints (towerClosureAlgEquiv (K := K) (L := L) (Ω := Ω)).symm
    (RestrictedPoints K L Ω X)

/-- The actual finite-flat model survives both integral and closure base change. -/
theorem IsFiniteFlat.baseChange_towerClosure (hX : IsFiniteFlat R K Ω X) :
    IsFiniteFlat S L (AlgebraicClosure L) (TowerClosurePoints (K := K) (L := L) (Ω := Ω)
      (X := X)) :=
  (hX.baseChange_sameClosure (S := S) (L := L)).closureChange
    (towerClosureAlgEquiv (K := K) (L := L) (Ω := Ω)).symm

/-- Tower transport acts by the same original automorphism on the original point group. -/
theorem towerClosurePoints_smul (σ : Ω ≃ₐ[K] Ω)
    (hσ : ∀ a : L, σ (algebraMap L Ω a) = algebraMap L Ω a) (x : X) :
    @SMul.smul _ (TowerClosurePoints (K := K) (L := L) (Ω := Ω) (X := X)) inferInstance
      (towerAutomorphism (IsScalarTower.toAlgHom K L Ω) σ hσ) x = σ • x := by
  change (AlgEquiv.autCongr (towerClosureAlgEquiv (K := K) (L := L) (Ω := Ω))
    (towerAutomorphism _ σ hσ)).restrictScalars K • x = _
  rw [towerClosureAlgEquiv_autCongr]
  rfl

end GaloisModule
