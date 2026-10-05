/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.NodeTangentSplitComponent

/-!
# The nonsplit nodal component bound from coefficient tests

Construct the quadratic tangent field and its integral DVR, rather than
assuming an extension or a component action. The exact finite-depth tests
then imply that the original rational component quotient is finite, is
killed by two, and has at most two elements.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve IsLocalRing

universe u

variable {K : Type u} [Field K] (A : ValuationSubring K) [IsDiscreteValuationRing A]
  (W : WeierstrassCurve A) [(W.map (algebraMap A K)).IsElliptic]

/-- The nonsplit nodal coefficient tests give the rational component bound at most two. -/
theorem nonsplitNode_components
    (hirr : Irreducible ((nodeTangentPolynomial W).map (residue A)))
    {π : A} {n : ℕ} (hn : 0 < n) (hπ0 : π ≠ 0)
    (hπ : maximalIdeal A = Ideal.span {π}) (hb : IsUnit W.b₂)
    (h3 : W.a₃ ∈ maximalIdeal A ^ (n + 1))
    (h4 : W.a₄ ∈ maximalIdeal A ^ (n + 1))
    (h6 : W.a₆ ∈ maximalIdeal A ^ n)
    (h6' : W.a₆ ∉ maximalIdeal A ^ (n + 1)) :
    Finite (EllipticComponentQuotient A W) ∧
      (∀ c : EllipticComponentQuotient A W, 2 • c = 0) ∧
      Nat.card (EllipticComponentQuotient A W) ≤ 2 := by
  obtain ⟨hdom, hdvr, hlocal, _, L, hfield, halgK, _, _, halgA, htowerK,
    halgS, htowerS, hfrac, _, _⟩ := exists_node_tangent_fraction_field K W hirr hb π hπ
  let := hdom
  let := hdvr
  let := hlocal
  let := hfield
  let := halgK
  let := halgA
  let := htowerK
  let := halgS
  let := htowerS
  let := hfrac
  have D := nodeTangentValuationShear_splitNodeDepth A W L hirr hn hπ0 hπ hb h3 h4 h6 h6'
  exact ⟨finite_ellipticComponentQuotient_of_tangentDepth A W L D,
    two_nsmul_nodeTangentComponent_eq_zero A W L D,
    natCard_ellipticComponentQuotient_le_two_of_tangentDepth A W L D⟩

end FLT.Mazur
