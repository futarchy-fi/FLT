/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UnpointedLocalAcyclicEffectiveDescent

/-!
# Detecting the intrinsic condition on a supplied full Cartier divisor

Local acyclic membership of the actual Picard-sheaf class detects the
cohomology and rank-one direct image of the supplied divisor itself.
Consequently equality with an acyclic sheaf section determines every
relative Cartier competitor, without assuming its acyclicity in advance.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.CartierAbel
open FCurve SchemePicard
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X : Scheme} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  (T : Over (Spec (.of R))) (D : Divisor (pullback f T.hom))
  (hD : Flat (D.val.subschemeι ≫ pullback.snd f T.hom))

include hD in
/-- Local acyclic membership detects the intrinsic conditions of the full given divisor. -/
theorem relativeDivisor_localAcyclic_iff :
    relativeFppfClass f T (abel (pullback.snd f T.hom) D) ∈
        (localGeometricAcyclicFppfSubfunctor f).obj (op T) ↔
      AcyclicRankOne (pullback.snd f T.hom) (divisorLineBundle D.val D.property) := by
  rw [localGeometricAcyclicFppf_class_iff]
  constructor
  · intro hc
    let E := finiteTypeTestClassDivisor (IsPullback.of_hasPullback f T.hom) _ hc
    have he : D = E.val :=
      finiteTypeTestClassDivisor_unique (IsPullback.of_hasPullback f T.hom) _ hc D hD rfl
    rw [he]
    exact E.property.2
  · intro hc
    exact (finiteTypeTestAbel (IsPullback.of_hasPullback f T.hom) ⟨D, hD, hc⟩).property

/-- A supplied relative divisor of an acyclic sheaf section is intrinsically acyclic. -/
def relativeDivisorOfLocalAcyclic
    (hc : relativeFppfClass f T (abel (pullback.snd f T.hom) D) ∈
      (localGeometricAcyclicFppfSubfunctor f).obj (op T)) :
    AcyclicRankOneRelativeDivisor (pullback.snd f T.hom) :=
  ⟨D, hD, (relativeDivisor_localAcyclic_iff f T D hD).mp hc⟩

include hD in
/-- Equality to an acyclic Abel section identifies every full relative Cartier competitor. -/
theorem relativeDivisor_eq_of_acyclic_fppfClass
    (E : AcyclicRankOneRelativeDivisor (pullback.snd f T.hom))
    (he : relativeFppfClass f T (abel (pullback.snd f T.hom) D) =
      relativeFppfClass f T (abel (pullback.snd f T.hom) E.val)) : D = E.val := by
  have hm : relativeFppfClass f T (abel (pullback.snd f T.hom) D) ∈
      (localGeometricAcyclicFppfSubfunctor f).obj (op T) := by
    rw [he]
    exact (relativeDivisor_localAcyclic_iff f T E.val E.property.1).mpr E.property.2
  have h : relativeDivisorOfLocalAcyclic f T D hD hm = E :=
    finiteTypeAcyclicAbelFppf_injective f T he
  exact congrArg Subtype.val h

end FLT.Mazur.CartierAbel
