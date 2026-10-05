/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.NodeTangentValuationConjugation
public import FLT.Mazur.EllipticNodeGaloisLabel

/-!
# The canonical tangent conjugation negates component labels

Specialize the semilinear point and component actions to the constructed
quadratic tangent field and its realized valuation subring. Uniformizer
fixing and compatibility are proved from integral conjugation.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve

variable {K : Type*} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)
  (L : Type*) [Field L]
  [IsDomain (AdjoinRoot (nodeTangentPolynomial W))]
  [IsDiscreteValuationRing (AdjoinRoot (nodeTangentPolynomial W))]
  [Algebra (AdjoinRoot (nodeTangentPolynomial W)) L]
  [IsFractionRing (AdjoinRoot (nodeTangentPolynomial W)) L]
  [Algebra A L] [IsScalarTower A (AdjoinRoot (nodeTangentPolynomial W)) L]
  [Algebra K L] [IsScalarTower A K L]

instance : IsLocalHom (nodeTangentValuationConjugation A W L).toRingHom := by
  constructor
  intro x hx
  have h := hx.map (nodeTangentValuationConjugation A W L).symm
  change IsUnit ((nodeTangentValuationConjugation A W L).symm
    (nodeTangentValuationConjugation A W L x)) at h
  simpa only [RingEquiv.symm_apply_apply] using h

/-- The canonical generic and integral conjugation maps form a compatible square. -/
theorem nodeTangentConjugation_compatible :
    (algebraMap (nodeTangentValuationSubring A W L) L).comp
        (nodeTangentValuationConjugation A W L).toRingHom =
      (nodeTangentFieldConjugation A W L).toRingHom.comp
        (algebraMap (nodeTangentValuationSubring A W L) L) := by
  apply RingHom.ext
  intro s
  exact (nodeTangentFieldConjugation_coe A W L s).symm

variable [DecidableEq L]
  [((nodeTangentValuationShear A W L).map
    (algebraMap (nodeTangentValuationSubring A W L) L)).IsElliptic]

/-- The actual semilinear point action of the canonical quadratic tangent conjugation. -/
noncomputable def nodeTangentGaloisPointAction :
    ((nodeTangentValuationShear A W L).map
      (algebraMap (nodeTangentValuationSubring A W L) L)).toProjective.Point →+
    ((nodeTangentValuationShear A W L).map
      (algebraMap (nodeTangentValuationSubring A W L) L)).toProjective.Point :=
  nodeGaloisPointAction _ _ (nodeTangentFieldConjugation A W L).toRingHom
    (nodeTangentValuationConjugation A W L).toRingHom
    (nodeTangentConjugation_compatible A W L) (nodeTangentValuationShear_conjugate A W L)

/-- Canonical quadratic tangent conjugation negates every actual point label. -/
theorem nodePointLabel_tangentGalois {π : A} {n : ℕ}
    (D : SplitNodeDepth (nodeTangentValuationShear A W L)
      (nodeTangentValuationEquiv A W L (algebraMap A _ π)) n)
    (P : ((nodeTangentValuationShear A W L).map
      (algebraMap (nodeTangentValuationSubring A W L) L)).toProjective.Point) :
    nodePointLabel D (nodeTangentGaloisPointAction A W L P) = -nodePointLabel D P :=
  nodePointLabel_galois _ _ _ _ _ _ D (nodeTangentValuationConjugation_base A W L π) P

/-- The canonical action on the actual component quotient of the split tangent model. -/
noncomputable def nodeTangentGaloisComponentAction {π : A} {n : ℕ}
    (D : SplitNodeDepth (nodeTangentValuationShear A W L)
      (nodeTangentValuationEquiv A W L (algebraMap A _ π)) n) :
    EllipticComponentQuotient (nodeTangentValuationSubring A W L)
        (nodeTangentValuationShear A W L) →+
      EllipticComponentQuotient (nodeTangentValuationSubring A W L)
        (nodeTangentValuationShear A W L) :=
  nodeGaloisComponentAction _ _ (nodeTangentFieldConjugation A W L).toRingHom
    (nodeTangentValuationConjugation A W L).toRingHom
    (nodeTangentConjugation_compatible A W L) (nodeTangentValuationShear_conjugate A W L)
    D (nodeTangentValuationConjugation_base A W L π)

/-- Canonical quadratic tangent conjugation negates actual component labels. -/
theorem nodeComponentLabel_tangentGalois {π : A} {n : ℕ}
    (D : SplitNodeDepth (nodeTangentValuationShear A W L)
      (nodeTangentValuationEquiv A W L (algebraMap A _ π)) n)
    (c : EllipticComponentQuotient (nodeTangentValuationSubring A W L)
      (nodeTangentValuationShear A W L)) :
    nodeComponentLabel D (nodeTangentGaloisComponentAction A W L D c) =
      -nodeComponentLabel D c :=
  nodeComponentLabel_galois _ _ _ _ _ _ D (nodeTangentValuationConjugation_base A W L π) c

/-- The canonical action is negation on the actual component quotient itself. -/
theorem nodeTangentGaloisComponentAction_eq_neg {π : A} {n : ℕ}
    (D : SplitNodeDepth (nodeTangentValuationShear A W L)
      (nodeTangentValuationEquiv A W L (algebraMap A _ π)) n)
    (c : EllipticComponentQuotient (nodeTangentValuationSubring A W L)
      (nodeTangentValuationShear A W L)) :
    nodeTangentGaloisComponentAction A W L D c = -c := by
  apply nodeComponentLabel_injective D
  rw [nodeComponentLabel_tangentGalois, nodeComponentLabel_neg]

/-- Applying the canonical action twice fixes every actual component class. -/
theorem nodeTangentGaloisComponentAction_involutive {π : A} {n : ℕ}
    (D : SplitNodeDepth (nodeTangentValuationShear A W L)
      (nodeTangentValuationEquiv A W L (algebraMap A _ π)) n) :
    Function.Involutive (nodeTangentGaloisComponentAction A W L D) := by
  intro c
  rw [nodeTangentGaloisComponentAction_eq_neg, nodeTangentGaloisComponentAction_eq_neg, neg_neg]

end FLT.Mazur
