/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.UnramifiedBaseChange
public import FLT.LocalClassFieldTheory.GaloisHomContinuity

/-!
# Galois restriction for unramified base change

The inclusion of unramified unions induces an actual continuous restriction
homomorphism of their Galois groups. Its action agrees with the field inclusion.
-/

@[expose] public noncomputable section

universe u

namespace LocalClassFieldTheory

open IsLocalRing

variable (R S K L C : Type u)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Algebra R S] [Module.Finite R S] [FaithfulSMul R S]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field L] [Algebra S L] [IsFractionRing S L] [Algebra K L] [Algebra R L]
  [Field C] [Algebra L C] [Algebra K C] [Algebra R C] [Algebra S C]
  [IsScalarTower K L C] [IsScalarTower R K C] [IsScalarTower R L C]
  [IsScalarTower S L C] [IsScalarTower R S C]
  [Algebra.IsSeparable K C] [Algebra.IsSeparable L C] [IsSepClosed C]
  [Finite (ResidueField R)] [Finite (ResidueField S)]
  [IsAdicComplete (maximalIdeal R) R] [IsAdicComplete (maximalIdeal S) S]

local notation "A" => maximalUnramified R K C
local notation "B" => maximalUnramified S L C

local instance baseChangeNormal : Normal K A := maximalUnramified_normal R K C

local instance baseChangeGalois : IsGalois L B := maximalUnramified_isGalois S L C

/-- The algebra structure induced by inclusion of the unramified unions. -/
local instance baseChangeAlgebra : Algebra A B :=
  (maximalUnramifiedBaseChange R S K L C).toAlgebra

local instance baseChangeTower : IsScalarTower K A B :=
  IsScalarTower.of_algebraMap_eq
    (fun x => (maximalUnramifiedBaseChange R S K L C).commutes x |>.symm)

/-- Galois restriction along the constructed inclusion of maximal unramified unions. -/
def unramifiedBaseChangeRestriction : Gal(B/L) →* Gal(A/K) :=
  (AlgEquiv.restrictNormalHom A).comp (AlgEquiv.restrictScalarsHom K)

/-- Restriction and the inclusion of fields give the actual commuting action square. -/
theorem unramifiedBaseChangeRestriction_apply (g : Gal(B/L)) (x : A) :
    maximalUnramifiedBaseChange R S K L C (unramifiedBaseChangeRestriction R S K L C g x) =
      g (maximalUnramifiedBaseChange R S K L C x) :=
  AlgEquiv.restrictNormal_commutes (g.restrictScalars K) A x

/-- The base-change Galois restriction is continuous for the Krull topologies. -/
theorem unramifiedBaseChangeRestriction_continuous :
    Continuous (unramifiedBaseChangeRestriction R S K L C) :=
  galoisHom_continuous (show A →+* B from (maximalUnramifiedBaseChange R S K L C).toRingHom)
    (unramifiedBaseChangeRestriction R S K L C)
    (unramifiedBaseChangeRestriction_apply R S K L C)

end LocalClassFieldTheory
