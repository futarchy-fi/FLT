/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteTypeTestAbelEquivalence

/-!
# Arbitrary test maps on the intrinsic acyclic divisor locus

The inverse Abel construction equips pullback with the actual direct-image
condition on every test. Its full ideal is exactly ideal comap along the
original total-space map. No section of the family is required here.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CartierAbel
open SchemePicard
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X : Scheme.{0}} (f : X ⟶ Spec (.of R))
  [IsProper f] [Flat f] [GeometricallyIntegral f]

/-- Pullback of a full acyclic divisor along an arbitrary original test-scheme map. -/
def finiteTypeAcyclicDivisorMap {T U : Over (Spec (.of R))} (g : T ⟶ U)
    (D : AcyclicRankOneRelativeDivisor (Limits.pullback.snd f U.hom)) :
    AcyclicRankOneRelativeDivisor (Limits.pullback.snd f T.hom) :=
  finiteTypeTestClassDivisor (IsPullback.of_hasPullback f T.hom)
    (relativeBaseMap f g (abel (Limits.pullback.snd f U.hom) D.val))
    (relativeGeometricAcyclicRankOne_map _ (relativeTotalMap_isPullback f g)
      (finiteTypeTestAbel (IsPullback.of_hasPullback f U.hom) D).property)

/-- The changed full divisor has exactly the pulled-back original Abel class. -/
theorem finiteTypeAcyclicDivisorMap_class {T U : Over (Spec (.of R))} (g : T ⟶ U)
    (D : AcyclicRankOneRelativeDivisor (Limits.pullback.snd f U.hom)) :
    abel (Limits.pullback.snd f T.hom) (finiteTypeAcyclicDivisorMap f g D).val =
      relativeBaseMap f g (abel (Limits.pullback.snd f U.hom) D.val) :=
  finiteTypeTestClassDivisor_class _ _ _

/-- Pullback preserves the entire ideal, including all nonreduced structure. -/
theorem finiteTypeAcyclicDivisorMap_ideal {T U : Over (Spec (.of R))} (g : T ⟶ U)
    (D : AcyclicRankOneRelativeDivisor (Limits.pullback.snd f U.hom)) :
    (finiteTypeAcyclicDivisorMap f g D).val.val = D.val.val.comap (relativeTotalMap f g) := by
  have h := finiteTypeTestClassDivisor_natural_ideal
    (IsPullback.of_hasPullback f U.hom)
    (finiteTypeTestAbel (IsPullback.of_hasPullback f U.hom) D).val
    (finiteTypeTestAbel (IsPullback.of_hasPullback f U.hom) D).property
    (IsPullback.of_hasPullback f T.hom) _
    (relativeGeometricAcyclicRankOne_map _ (relativeTotalMap_isPullback f g)
      (finiteTypeTestAbel (IsPullback.of_hasPullback f U.hom) D).property)
    (relativeTotalMap_isPullback f g) rfl
  change (finiteTypeAcyclicDivisorMap f g D).val.val = _ at h
  rw [finiteTypeTestAbel_left_inv] at h
  exact h

/-- Full-ideal extensionality for the actual intrinsic divisor type. -/
theorem acyclicRankOneRelativeDivisor_ext {Y S : Scheme.{0}} {q : Y ⟶ S}
    {D E : AcyclicRankOneRelativeDivisor q} (h : D.val.val = E.val.val) : D = E :=
  Subtype.ext (Subtype.ext h)

end FLT.Mazur.CartierAbel
