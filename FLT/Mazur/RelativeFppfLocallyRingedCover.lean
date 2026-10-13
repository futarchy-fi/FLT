/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeRelationFppfLocallyRingedDescent

/-!
# Locally ringed descent along any actual relative fppf cover

Use the actual scheme kernel pair to descend locally ringed morphisms.
No quasi-compactness or scheme condition on the target is required.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.RelativeFppfLocallyRingedCover
open RelativeRelationOrbit
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme.{u}} {U T : Over S} (g : U ⟶ T)
  [Flat g.left] [LocallyOfFinitePresentation g.left] [Surjective g.left]

/-- The actual scheme kernel pair has its constructed internal equivalence relation. -/
def kernelEquivalence : CategoryTheory.EquivalenceRelation
    (pullback.fst g g) (pullback.snd g g) :=
  IsKernelPair.equivalenceRelation g _ _ (pullbackIsPullback _ _) (IsPullback.of_hasPullback g g)

/-- Any relative fppf cover detects maps into arbitrary locally ringed spaces. -/
theorem epi : Epi g.left.toLRSHom :=
  fppfLocallyRinged_epi (kernelEquivalence g) g (IsPullback.of_hasPullback g g)

variable {Z : LocallyRingedSpace.{u}} (a : U.left.toLocallyRingedSpace ⟶ Z)
  (ha : (pullback.fst g g).left.toLRSHom ≫ a = (pullback.snd g g).left.toLRSHom ≫ a)

/-- Descent with compatibility checked on the actual scheme kernel pair. -/
def descend : T.left.toLocallyRingedSpace ⟶ Z :=
  fppfLocallyRingedDescend (kernelEquivalence g) g (IsPullback.of_hasPullback g g) a ha

/-- The descended morphism recovers its full locally ringed source map. -/
@[reassoc]
theorem descend_projection : g.left.toLRSHom ≫ descend g a ha = a :=
  fppfLocallyRingedDescend_projection (kernelEquivalence g) g (IsPullback.of_hasPullback g g) a ha

/-- This descent is unique on the structure sheaf as well as the carrier. -/
theorem descend_unique (b : T.left.toLocallyRingedSpace ⟶ Z)
    (hb : g.left.toLRSHom ≫ b = a) : b = descend g a ha :=
  fppfLocallyRingedDescend_unique (kernelEquivalence g) g (IsPullback.of_hasPullback g g) a ha b hb

end FLT.Mazur.RelativeFppfLocallyRingedCover
