/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonNormalizationDominant
public import FLT.Mazur.ProjectiveLineTopology

/-!
# Integrality of the actual pinched one-gon

The surjective normalization transfers irreducibility from the projective line.
Together with reducedness of the original affine atlas this proves integrality,
including at the pinched node.
-/

@[expose] public noncomputable section
open AlgebraicGeometry
universe u
namespace FLT.Mazur.OneGonIntegral
variable (K : Type u) [Field K]

/-- The actual one-gon is irreducible, by its surjective projective normalization. -/
instance irreducible : IrreducibleSpace (OneGonGluing.scheme K) :=
  (OneGonNormalizationFinite.normalization_surjective K).irreducibleSpace
    (OneGonNormalization.normalization K).continuous

/-- The original one-gon is integral even though its node is singular. -/
instance integral : IsIntegral (OneGonGluing.scheme K) :=
  isIntegral_of_irreducibleSpace_of_isReduced _

end FLT.Mazur.OneGonIntegral
