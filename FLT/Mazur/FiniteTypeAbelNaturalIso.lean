/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteTypeAcyclicDivisorPresheaf

/-!
# The intrinsic Abel correspondence as a natural isomorphism

The class of the positive divisor line identifies the full-divisor presheaf
with the geometric acyclic Picard subfunctor. Naturality is for all original
test morphisms, and the inverse has the established full-ideal comap formula.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.CartierAbel
open SchemePicard
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X : Scheme.{0}} (f : X ⟶ Spec (.of R))
  [IsProper f] [Flat f] [GeometricallyIntegral f]

/-- The original Abel map is a natural isomorphism on the intrinsic acyclic locus. -/
def finiteTypeAbelNaturalIso : finiteTypeAcyclicDivisorPresheaf f ⋙ uliftFunctor.{1} ≅
    (geometricAcyclicPicardSubfunctor f).toFunctor :=
  NatIso.ofComponents (fun T ↦
    (Equiv.ulift.trans
      (finiteTypeTestAbelEquiv (IsPullback.of_hasPullback f T.unop.hom))).toIso)
    (fun {T U} g ↦ by
      apply ConcreteCategory.hom_ext
      intro D
      exact Subtype.ext (finiteTypeAcyclicDivisorMap_class f g.unop D.down))

/-- The comparison takes exactly the Abel class of the actual full Cartier divisor. -/
lemma finiteTypeAbelNaturalIso_class (T : Over (Spec (.of R)))
    (D : AcyclicRankOneRelativeDivisor (Limits.pullback.snd f T.hom)) :
    ((finiteTypeAbelNaturalIso f).hom.app (op T) (ULift.up D)).val =
      abel (Limits.pullback.snd f T.hom) D.val := rfl

/-- The natural inverse recovers the full original divisor from an independent class. -/
lemma finiteTypeAbelNaturalIso_inverse (T : Over (Spec (.of R)))
    (c : (geometricAcyclicPicardSubfunctor f).toFunctor.obj (op T)) :
    ((finiteTypeAbelNaturalIso f).inv.app (op T) c).down =
      finiteTypeTestClassDivisor (IsPullback.of_hasPullback f T.hom) c.val c.property := rfl

end FLT.Mazur.CartierAbel
