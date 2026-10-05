/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.NodeTangentShearRealization
public import FLT.Mazur.EllipticShearedComponentExtension
public import FLT.Mazur.EllipticNodeComponentCyclic

/-!
# The original rational components in the split tangent model

The canonical component injection lands in the realized split model after
inverse root shearing. Its image is fixed by the canonical tangent action,
hence is killed by two. Cyclicity then bounds the original quotient by two.
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
  [(W.map (algebraMap A K)).IsElliptic]

instance nodeTangentBaseChange_isElliptic :
    ((W.map (nodeTangentValuationBaseMap A W L)).map
      (algebraMap (nodeTangentValuationSubring A W L) L)).IsElliptic := by
  have h : (W.map (algebraMap A K)).map (algebraMap K L) =
      (W.map (nodeTangentValuationBaseMap A W L)).map
        (algebraMap (nodeTangentValuationSubring A W L) L) := by
    rw [map_map, map_map, nodeTangentValuationBaseMap_compatible]
  rw [← h]
  infer_instance

instance nodeTangentValuationShear_isElliptic :
    ((nodeTangentValuationShear A W L).map
      (algebraMap (nodeTangentValuationSubring A W L) L)).IsElliptic := by
  rw [nodeTangentValuationShear_eq_rootShear, ← map_variableChange]
  infer_instance

variable [DecidableEq L]
  [IsLocalHom (algebraMap A (AdjoinRoot (nodeTangentPolynomial W)))]

/-- Extend rational components and apply the inverse realized root shear. -/
noncomputable def nodeTangentSplitComponentExtension :
    EllipticComponentQuotient A W →+
      EllipticComponentQuotient (nodeTangentValuationSubring A W L)
        (nodeTangentValuationShear A W L) :=
  shearedComponentExtension _ (nodeTangentValuationRoot A W L) _ A W
    (algebraMap K L) (nodeTangentValuationBaseMap A W L)
    (nodeTangentValuationBaseMap_compatible A W L)
    (nodeTangentValuationShear_eq_rootShear A W L)

/-- The canonical injection into the split model loses no rational components. -/
theorem nodeTangentSplitComponentExtension_injective :
    Function.Injective (nodeTangentSplitComponentExtension A W L) :=
  shearedComponentExtension_injective _ _ _ _ _ _ _ _ _

/-- The image of every original rational component is fixed by tangent conjugation. -/
theorem nodeTangentSplitComponentExtension_fixed {π : A} {n : ℕ}
    (D : SplitNodeDepth (nodeTangentValuationShear A W L)
      (nodeTangentValuationEquiv A W L (algebraMap A _ π)) n)
    (c : EllipticComponentQuotient A W) :
    nodeTangentGaloisComponentAction A W L D (nodeTangentSplitComponentExtension A W L c) =
      nodeTangentSplitComponentExtension A W L c :=
  shearedComponentExtension_fixed _ _ _ _ _ _ _ _
    (nodeTangentFieldConjugation A W L).toRingHom
    (nodeTangentValuationConjugation A W L).toRingHom
    (nodeTangentConjugation_compatible A W L) (nodeTangentValuationShear_conjugate A W L)
    (nodeTangentValuationShear_eq_rootShear A W L)
    (nodeTangentValuationRoot_field_conjugate A W L)
    (fun x => (nodeTangentFieldConjugation A W L).commutes x) D
    (nodeTangentValuationConjugation_base A W L π) c

omit [DecidableEq L] in
/-- Every original rational component is killed by two. -/
theorem two_nsmul_nodeTangentComponent_eq_zero {π : A} {n : ℕ}
    (D : SplitNodeDepth (nodeTangentValuationShear A W L)
      (nodeTangentValuationEquiv A W L (algebraMap A _ π)) n)
    (c : EllipticComponentQuotient A W) : 2 • c = 0 := by
  classical
  apply nodeTangentSplitComponentExtension_injective A W L
  rw [map_nsmul, map_zero, two_nsmul]
  have h := nodeTangentSplitComponentExtension_fixed A W L D c
  rw [nodeTangentGaloisComponentAction_eq_neg] at h
  exact neg_eq_iff_add_eq_zero.mp h

omit [DecidableEq L] in
/-- Finiteness descends through the actual component injection into the split model. -/
theorem finite_ellipticComponentQuotient_of_tangentDepth {π : A} {n : ℕ}
    (D : SplitNodeDepth (nodeTangentValuationShear A W L)
      (nodeTangentValuationEquiv A W L (algebraMap A _ π)) n) :
    Finite (EllipticComponentQuotient A W) := by
  classical
  let := finite_ellipticComponentQuotient_of_splitNodeDepth D
  exact Finite.of_injective _ (nodeTangentSplitComponentExtension_injective A W L)

omit [DecidableEq L] in
/-- The actual original component group has at most two elements in the nonsplit tangent case. -/
theorem natCard_ellipticComponentQuotient_le_two_of_tangentDepth {π : A} {n : ℕ}
    (D : SplitNodeDepth (nodeTangentValuationShear A W L)
      (nodeTangentValuationEquiv A W L (algebraMap A _ π)) n) :
    Nat.card (EllipticComponentQuotient A W) ≤ 2 := by
  classical
  let := finite_ellipticComponentQuotient_of_splitNodeDepth D
  let := Finite.of_injective _ (nodeTangentSplitComponentExtension_injective A W L)
  let := Fintype.ofFinite (EllipticComponentQuotient A W)
  let := isAddCyclic_ellipticComponentQuotient_of_splitNodeDepth D
  let := isAddCyclic_of_injective (nodeTangentSplitComponentExtension A W L)
    (nodeTangentSplitComponentExtension_injective A W L)
  simpa only [two_nsmul_nodeTangentComponent_eq_zero A W L D, Finset.filter_true,
    Finset.card_univ, Nat.card_eq_fintype_card] using
    (IsAddCyclic.card_nsmul_eq_zero_le (α := EllipticComponentQuotient A W)
      (show 0 < 2 by decide))

end FLT.Mazur
