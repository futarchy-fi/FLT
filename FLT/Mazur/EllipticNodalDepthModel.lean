/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodalDiscriminantDepth
public import FLT.Mazur.EllipticSplitNodeComponents

/-!
# Constructing exact nodal depth before splitting the tangent

Generic ellipticity and bad multiplicative reduction construct the positive
finite discriminant depth, a uniformizer, and an integral translation with
exact a₆ depth. No rational tangent, completeness or henselianity is assumed.
-/

@[expose] public section
open WeierstrassCurve IsLocalRing
namespace FLT.Mazur

/-- Construct all coefficient hypotheses needed by the quadratic tangent extension. -/
theorem exists_nodalDepth_model {K : Type*} [Field K]
    (A : ValuationSubring K) [IsDiscreteValuationRing A] [PerfectField (ResidueField A)]
    (W : WeierstrassCurve A) [(W.map (algebraMap A K)).IsElliptic]
    (hΔ : W.Δ ∈ maximalIdeal A) (hc : IsUnit W.c₄) :
    ∃ (n : ℕ) (π r t : A), 0 < n ∧ π ≠ 0 ∧ maximalIdeal A = Ideal.span {π} ∧
      W.Δ ∈ maximalIdeal A ^ n ∧ W.Δ ∉ maximalIdeal A ^ (n + 1) ∧
      let V := (VariableChange.mk 1 r 0 t : VariableChange A) • W
      IsUnit V.b₂ ∧ V.a₃ ∈ maximalIdeal A ^ (n + 1) ∧
        V.a₄ ∈ maximalIdeal A ^ (n + 1) ∧ V.a₆ ∈ maximalIdeal A ^ n ∧
          V.a₆ ∉ maximalIdeal A ^ (n + 1) := by
  have hΔ0 : W.Δ ≠ 0 := by
    intro hz
    apply (W.map (algebraMap A K)).isUnit_Δ.ne_zero
    simp [map_Δ, hz]
  obtain ⟨n, hn, hd, hd'⟩ := exists_positive_maximalIdeal_depth hΔ0 hΔ
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  obtain ⟨r, t, hv⟩ := exists_nodal_discriminant_depth W n hn hd hd' hc
  exact ⟨n, π, r, t, hn, hπ.ne_zero, hπ.maximalIdeal_eq, hd, hd', hv⟩

end FLT.Mazur
