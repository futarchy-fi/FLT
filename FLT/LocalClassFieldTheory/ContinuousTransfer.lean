/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.TransferRestrictionHomotopy
public import Mathlib.Topology.ContinuousMap.Algebra

/-!
# Continuous finite-index transfer in low degrees

For an open subgroup the coset sum and the restriction-transfer homotopy
are continuous. Thus continuous cocycles and continuous boundaries transfer.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open groupCohomology

variable {G M : Type*} [Group G] [AddCommGroup M] [DistribMulAction G M]
  [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousSMul G M]
  (H : Subgroup G) [Fintype (G ⧸ H)] (hH : IsOpen (H : Set G))

/-- Transfer of a continuous one-cochain. -/
def continuousTransferOne (b : C(H, M)) : C(G, M) :=
  ⟨transferOne H b, continuous_finsetSum _ fun q _ =>
    continuous_const.smul (b.continuous.comp (continuous_transferTransport H hH q))⟩

/-- Transfer of a continuous two-cochain. -/
def continuousTransferTwo (c : C(H × H, M)) : C(G × G, M) := by
  let : DiscreteTopology (G ⧸ H) := QuotientGroup.discreteTopology hH
  have ht : Continuous (fun p : G × (G ⧸ H) => transferTransport H p.1 p.2) :=
    continuous_prod_of_discrete_right.mpr (continuous_transferTransport H hH)
  refine ⟨transferTwo H c, continuous_finsetSum _ fun q _ => ?_⟩
  exact continuous_const.smul (c.continuous.comp
    (((continuous_transferTransport H hH q).comp continuous_fst).prodMk
      (ht.comp (continuous_snd.prodMk
        ((continuous_transferCoset H q).comp continuous_fst)))))

/-- The explicit restriction-transfer homotopy is continuous. -/
def continuousTransferRestrictionHomotopy (c : C(G × G, M)) : C(G, M) :=
  ⟨transferRestrictionHomotopy H c, continuous_finsetSum _ fun q _ =>
    (c.continuous.comp (continuous_const.prodMk (continuous_subtype_val.comp
      (continuous_transferTransport H hH q)))).sub
      (c.continuous.comp (continuous_id.prodMk
        ((continuous_transferRepresentative H hH).comp (continuous_transferCoset H q))))⟩

/-- Continuous transfer preserves the two-cocycle equation. -/
theorem continuousTransferTwo_isCocycle (c : C(H × H, M)) (hc : IsCocycle₂ c) :
    IsCocycle₂ (continuousTransferTwo H hH c) := transferTwo_isCocycle H c hc

/-- Transfer takes a continuous bounding cochain to a continuous bounding cochain. -/
theorem continuousTransferTwo_boundary (c : C(H × H, M)) (b : C(H, M))
    (hb : ∀ g h : H, c (g, h) = g • b h - b (g * h) + b g) (g h : G) :
    continuousTransferTwo H hH c (g, h) =
      g • continuousTransferOne H hH b h - continuousTransferOne H hH b (g * h) +
        continuousTransferOne H hH b g := by
  change transferTwo H c (g, h) = _
  have he : (c : H × H → M) = fun p => p.1 • b p.2 - b (p.1 * p.2) + b p.1 :=
    funext fun p => hb p.1 p.2
  rw [he]
  exact transferTwo_boundary H b g h

omit [ContinuousSMul G M] in
/-- The restriction-degree identity has a continuous coboundary witness. -/
theorem continuousTransferTwo_restriction (c : C(G × G, M)) (hc : IsCocycle₂ c)
    (g h : G) :
    transferTwo H (fun p => c (p.1, p.2)) (g, h) =
      Fintype.card (G ⧸ H) • c (g, h) +
        (g • continuousTransferRestrictionHomotopy H hH c h -
          continuousTransferRestrictionHomotopy H hH c (g * h) +
            continuousTransferRestrictionHomotopy H hH c g) :=
  transferTwo_restriction H c hc g h

end LocalClassFieldTheory
