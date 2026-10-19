/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodalDepthModel
public import FLT.Mazur.NodeTangentSplittingAlternative
public import FLT.Mazur.NodeTangentSplitDepthExtension

/-!
# A split-depth model after an extension of degree at most two

Bad discriminant and invertible c₄ on the original elliptic local equation
construct a split-depth model. Both tangent cases are handled. The output
retains the coefficient map, its exact valuation restriction, and the entire
integral variable change, so original maps can be transported to this model.
-/

@[expose] public noncomputable section
open WeierstrassCurve IsLocalRing
namespace FLT.Mazur

/-- Construct split depth, including tangent splitting, from the original nodal invariants. -/
theorem exists_splitDepth_extension {K : Type} [Field K]
    (A : ValuationSubring K) [IsDiscreteValuationRing A] [PerfectField (ResidueField A)]
    (W : WeierstrassCurve A) [(W.map (algebraMap A K)).IsElliptic]
    (hΔ : W.Δ ∈ maximalIdeal A) (hc : IsUnit W.c₄) :
    ∃ (n : ℕ) (π : A), W.Δ ∈ maximalIdeal A ^ n ∧ W.Δ ∉ maximalIdeal A ^ (n + 1) ∧
      ∃ (L : Type) (_ : Field L) (_ : Algebra K L) (_ : Module.Finite K L)
        (_ : Algebra.IsSeparable K L) (B : ValuationSubring L)
        (_ : IsDiscreteValuationRing B) (_ : PerfectField (ResidueField B))
        (φ : A →+* B) (T : VariableChange B), IsLocalHom φ ∧
        (∀ a : A, (φ a : L) = algebraMap K L a) ∧ B.comap (algebraMap K L) = A ∧
        Module.finrank K L ≤ 2 ∧ T.u = 1 ∧ SplitNodeDepth (T • W.map φ) (φ π) n := by
  obtain ⟨n, π, r, t, hn, hπ0, hπ, hd, hd', hb, h3, h4, h6, h6'⟩ :=
    exists_nodalDepth_model A W hΔ hc
  let Q : VariableChange A := .mk 1 r 0 t
  let V := Q • W
  have halt := residue_node_split_or_irreducible V
    (Ideal.pow_le_self (by omega) h3) (Ideal.pow_le_self (by omega) h4)
    (Ideal.pow_le_self (by omega) h6)
  refine ⟨n, π, hd, hd', ?_⟩
  rcases halt with hs | hi
  · have hsW : (W.nodePoly.map (residue A)).Splits :=
      (nodePoly_map_splits_smul_iff (residue A) W Q).mp hs
    obtain ⟨r', s', t', h1, h2, h3', h4', h6'', h6'''⟩ :=
      exists_split_node_discriminant_depth W n hn hd hd' hc hsW
    refine ⟨K, inferInstance, inferInstance, inferInstance, inferInstance,
      A, inferInstance, inferInstance, RingHom.id A, .mk 1 r' s' t',
      inferInstance, (fun _ ↦ rfl), ?_, ?_, rfl, ?_⟩
    · ext x
      rfl
    · simp
    · simpa only [WeierstrassCurve.map_id, RingHom.id_apply] using
        (show SplitNodeDepth ((VariableChange.mk 1 r' s' t' : VariableChange A) • W) π n from
          ⟨hn, hπ0, hπ, h1, h2, h3', h4', h6'', h6'''⟩)
  · obtain ⟨L, field, alg, fin, sep, B, dvr, perf, φ, s, loc, hφ, hB, rank, depth⟩ :=
      exists_nodeTangent_splitDepth_extension A V hi hn hπ0 hπ hb h3 h4 h6 h6'
    let _ := field
    let _ := alg
    let _ := fin
    let _ := sep
    let _ := dvr
    let _ := perf
    let T : VariableChange B := .mk 1 0 s 0 * Q.map φ
    refine ⟨L, field, alg, fin, sep, B, dvr, perf, φ, T, loc, hφ, hB,
      rank.le, ?_, ?_⟩
    · simp [T, Q, VariableChange.mul_def, VariableChange.map]
    · simpa only [T, V, map_variableChange, mul_smul] using depth

end FLT.Mazur
