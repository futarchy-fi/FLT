/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.NodeTangentFractionField
public import FLT.Mazur.ValuationRingModel
public import FLT.Mazur.EllipticComponentBaseChange

/-!
# The tangent DVR as an actual valuation subring

The structures supplied by `exists_node_tangent_fraction_field` give a valuation
subring of the quadratic field, a compatible local base map, and an injective
comparison of the actual component quotients. The tangent shear retains its
exact nodal depth in this realization.
-/

@[expose] public section

namespace FLT.Mazur

open IsLocalRing WeierstrassCurve

variable {K : Type*} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)
  (L : Type*) [Field L]
  [IsDomain (AdjoinRoot (nodeTangentPolynomial W))]
  [IsDiscreteValuationRing (AdjoinRoot (nodeTangentPolynomial W))]
  [Algebra (AdjoinRoot (nodeTangentPolynomial W)) L]
  [IsFractionRing (AdjoinRoot (nodeTangentPolynomial W)) L]

/-- The integral tangent algebra, realized in its quadratic fraction field. -/
noncomputable abbrev nodeTangentValuationSubring : ValuationSubring L :=
  fractionValuationSubring (AdjoinRoot (nodeTangentPolynomial W)) L

/-- The canonical equivalence from the abstract tangent DVR to its realization. -/
noncomputable abbrev nodeTangentValuationEquiv :
    AdjoinRoot (nodeTangentPolynomial W) ≃+* nodeTangentValuationSubring A W L :=
  fractionValuationEquiv _ L

/-- The tangent shear as an equation over the actual valuation subring. -/
noncomputable def nodeTangentValuationShear :
    WeierstrassCurve (nodeTangentValuationSubring A W L) :=
  (nodeTangentShear W).map (nodeTangentValuationEquiv A W L).toRingHom

/-- Exact split nodal depth survives realization inside the generic field. -/
theorem nodeTangentValuationShear_splitNodeDepth
    (hirr : Irreducible ((nodeTangentPolynomial W).map (residue A)))
    {π : A} {n : ℕ} (hn : 0 < n) (hπ0 : π ≠ 0)
    (hπ : maximalIdeal A = Ideal.span {π}) (hb : IsUnit W.b₂)
    (h3 : W.a₃ ∈ maximalIdeal A ^ (n + 1))
    (h4 : W.a₄ ∈ maximalIdeal A ^ (n + 1))
    (h6 : W.a₆ ∈ maximalIdeal A ^ n)
    (h6' : W.a₆ ∉ maximalIdeal A ^ (n + 1)) :
    SplitNodeDepth (nodeTangentValuationShear A W L)
      (nodeTangentValuationEquiv A W L (algebraMap A _ π)) n :=
  (nodeTangentShear_splitNodeDepth W hirr hn hπ0 hπ hb h3 h4 h6 h6').ringEquiv
    (nodeTangentValuationEquiv A W L)

variable [Algebra A L] [IsScalarTower A (AdjoinRoot (nodeTangentPolynomial W)) L]
  [Algebra K L] [IsScalarTower A K L]

/-- The original valuation ring embeds locally into the realized tangent DVR. -/
noncomputable abbrev nodeTangentValuationBaseMap : A →+* nodeTangentValuationSubring A W L :=
  fractionValuationBaseMap

/-- The integral tangent extension and the generic field extension are compatible. -/
theorem nodeTangentValuationBaseMap_compatible :
    (algebraMap (nodeTangentValuationSubring A W L) L).comp
        (nodeTangentValuationBaseMap A W L) =
      (algebraMap K L).comp (algebraMap A K) := by
  ext a
  exact (fractionValuationBaseMap_coe a).trans (IsScalarTower.algebraMap_apply A K L a)

variable [IsLocalHom (algebraMap A (AdjoinRoot (nodeTangentPolynomial W)))]

/-- The actual component map into the quadratic tangent extension. -/
noncomputable def nodeTangentComponentExtension :
    EllipticComponentQuotient A W →+
      EllipticComponentQuotient (nodeTangentValuationSubring A W L)
        (W.map (nodeTangentValuationBaseMap A W L)) :=
  integralComponentExtension A _ W (algebraMap K L) (nodeTangentValuationBaseMap A W L)
    (nodeTangentValuationBaseMap_compatible A W L)

/-- No original rational component disappears in the tangent extension. -/
theorem nodeTangentComponentExtension_injective :
    Function.Injective (nodeTangentComponentExtension A W L) :=
  integralComponentExtension_injective A _ W _ _ _

end FLT.Mazur
