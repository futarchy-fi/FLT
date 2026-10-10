/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassAuxiliaryNormalizationGroup
public import FLT.Mazur.GroupMarkingTransport

/-!
# Full auxiliary group markings under canonical normalization

The abstract transport of markings is applied to the already proved actual
normalization group isomorphism. It preserves the whole homomorphism,
including order-four equations and injectivity on each test scheme.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MonObj

namespace FLT.Mazur.UniversalWeierstrass

attribute [local irreducible] auxiliaryPullbackGroup auxiliaryNormalizedGroup
  auxiliaryNormalizationGroupIso

variable {R : Type} [CommRing R] (g : AuxiliarySectionRing →+* R)
  {T : Over (Spec (.of R))}

/-- The actual normalization gives a bijection of complete auxiliary group markings. -/
def auxiliaryMarkingNormalizationEquiv :
    (Labels 4 →* (T ⟶ (auxiliaryPullbackGroup g).X)) ≃
      (Labels 4 →* (T ⟶ (auxiliaryNormalizedGroup g).X)) :=
  GroupMarkingTransport.markingEquiv (L := Labels 4) (T := T)
    (auxiliaryPullbackGroup g) (auxiliaryNormalizedGroup g)
    (auxiliaryNormalizationGroupIso g).symm

end FLT.Mazur.UniversalWeierstrass
