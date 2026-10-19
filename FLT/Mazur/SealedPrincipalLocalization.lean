/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# A sealed principal localization

Cache the algebraic structures before specializing to nested coordinate rings.
The localization universal property remains available without unfolding the
quotient representation of its carrier in later geometric proofs.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.SealedPrincipalLocalization

variable {R : Type*} [CommRing R] (r : R)

/-- The actual principal localization with a sealed carrier. -/
def Ring := Localization.Away r

/-- The original localization ring operations. -/
instance ringCommRing : CommRing (Ring r) := inferInstanceAs (CommRing (Localization.Away r))

/-- The original localization scalar map. -/
instance ringAlgebra : Algebra R (Ring r) := inferInstanceAs (Algebra R (Localization.Away r))

/-- The universal property of the original localization. -/
instance ringLocalization : IsLocalization.Away r (Ring r) :=
  inferInstanceAs (IsLocalization.Away r (Localization.Away r))

variable {A : Type*} [CommRing A] [Algebra A R]

/-- The original coefficient map through the source algebra. -/
instance ringBaseAlgebra : Algebra A (Ring r) :=
  inferInstanceAs (Algebra A (Localization.Away r))

/-- Compatibility of the coefficient and localization maps. -/
instance ringScalarTower : IsScalarTower A R (Ring r) :=
  inferInstanceAs (IsScalarTower A R (Localization.Away r))

attribute [irreducible] Ring

end FLT.Mazur.SealedPrincipalLocalization
