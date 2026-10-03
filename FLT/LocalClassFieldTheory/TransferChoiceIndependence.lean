/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.TransferRepresentativeChange
public import FLT.LocalClassFieldTheory.ContinuousCorestrictionH2

/-!
# Continuous transfer is independent of the representatives

An arbitrary subgroup-valued change of coset representatives gives a continuous
transfer and a continuous comparison homotopy. Its class is the constructed
corestriction. Every section of the coset projection has this form.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open groupCohomology

variable {G M : Type} [Group G] [AddCommGroup M] [DistribMulAction G M]
  [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul G M] (H : Subgroup G) [CompactSpace H]
  [Fintype (G ⧸ H)] (hH : IsOpen (H : Set G)) (k : G ⧸ H → H)

omit [CompactSpace G] [TotallyDisconnectedSpace G] [CompactSpace H] [Fintype (G ⧸ H)] in
include hH in
/-- The changed subgroup transport remains continuous. -/
theorem continuous_transferTransportUsing (q : G ⧸ H) :
    Continuous (fun g => transferTransportUsing H k g q) := by
  let : DiscreteTopology (G ⧸ H) := QuotientGroup.discreteTopology hH
  exact (continuous_const.mul (continuous_transferTransport H hH q)).mul
    (continuous_of_discreteTopology.comp (continuous_transferCoset H q))

/-- Continuous transfer using any subgroup-valued change of representatives. -/
def continuousTransferTwoUsing (c : C(H × H, M)) : C(G × G, M) := by
  let : DiscreteTopology (G ⧸ H) := QuotientGroup.discreteTopology hH
  have ht : Continuous (fun p : G × (G ⧸ H) => transferTransportUsing H k p.1 p.2) :=
    continuous_prod_of_discrete_right.mpr (continuous_transferTransportUsing H hH k)
  refine ⟨transferTwoUsing H k c, continuous_finsetSum _ fun q _ => ?_⟩
  exact continuous_const.smul (c.continuous.comp
    (((continuous_transferTransportUsing H hH k q).comp continuous_fst).prodMk
      (ht.comp (continuous_snd.prodMk
        ((continuous_transferCoset H q).comp continuous_fst)))))

/-- The comparison between choices is a continuous one-cochain. -/
def continuousTransferRepresentativeHomotopy (c : C(H × H, M)) : C(G, M) := by
  let : DiscreteTopology (G ⧸ H) := QuotientGroup.discreteTopology hH
  refine ⟨transferRepresentativeHomotopy H k c, continuous_finsetSum _ fun q _ => ?_⟩
  exact continuous_const.smul
    ((c.continuous.comp (continuous_const.prodMk
      (continuous_transferTransportUsing H hH k q))).sub
        (c.continuous.comp ((continuous_transferTransport H hH q).prodMk
          (continuous_of_discreteTopology.comp (continuous_transferCoset H q)))))

/-- Every changed representative sum gives the same class in actual continuous H2. -/
theorem continuousTransfer_choice_independent (c : C(H × H, M)) (hc : IsCocycle₂ c) :
    integralH2Class (continuousTransferTwoUsing H hH k c) (transferTwoUsing_isCocycle H k c hc) =
      continuousCorestrictionH2 H hH (integralH2Class c hc) := by
  rw [continuousCorestrictionH2_class]
  apply (integralH2Class_eq_iff _ _ _ _).mpr
  refine ⟨continuousTransferRepresentativeHomotopy H hH k c, fun g h => ?_⟩
  change g • transferRepresentativeHomotopy H k c h -
    transferRepresentativeHomotopy H k c (g * h) + transferRepresentativeHomotopy H k c g =
    transferTwoUsing H k c (g, h) - transferTwo H c (g, h)
  rw [transferTwoUsing_eq H k c hc]
  abel

end LocalClassFieldTheory
