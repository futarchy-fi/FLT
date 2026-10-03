/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.ContinuousTransfer
public import FLT.LocalClassFieldTheory.IntegralTwoClassAdditive

/-!
# Corestriction on actual continuous H2

The finite coset sum descends through the surjective cocycle-class map.
The descent uses the proved continuous boundary formula.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open groupCohomology

variable {G M : Type} [Group G] [AddCommGroup M] [DistribMulAction G M]
  [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul G M] (H : Subgroup G) [CompactSpace H]
  [Fintype (G ⧸ H)] (hH : IsOpen (H : Set G))

/-- Transfer as an additive map of the continuous cocycle groups. -/
def continuousTransferCocycles : continuousTwoCocycles (G := H) (M := M) →+
    continuousTwoCocycles (G := G) (M := M) where
  toFun c := ⟨continuousTransferTwo H hH c.val,
    continuousTransferTwo_isCocycle H hH c.val c.property⟩
  map_zero' := by
    apply Subtype.ext
    ext p
    simp [continuousTransferTwo, transferTwo]
  map_add' c d := by
    apply Subtype.ext
    ext p
    simp [continuousTransferTwo, transferTwo, smul_add, Finset.sum_add_distrib]

/-- The continuous boundary formula proves the kernel condition for descent. -/
theorem continuousTransferCocycles_ker :
    (integralH2ClassHom (G := H) (M := M)).ker ≤
      (integralH2ClassHom.comp (continuousTransferCocycles H hH)).ker := by
  intro c hc
  obtain ⟨b, hb⟩ := (integralH2Class_eq_zero c.val c.property).mp hc
  apply (integralH2Class_eq_zero _ (continuousTransferCocycles H hH c).property).mpr
  refine ⟨continuousTransferOne H hH b, fun g h => ?_⟩
  exact (continuousTransferTwo_boundary H hH c.val b (fun g h => (hb g h).symm) g h).symm

/-- Corestriction induced by the actual finite coset sum of continuous cocycles. -/
def continuousCorestrictionH2 : continuousCohomology ℤ H M 2 →+
    continuousCohomology ℤ G M 2 :=
  (integralH2ClassHom (G := H) (M := M)).liftOfSurjective
    integralH2ClassHom_surjective
    ⟨integralH2ClassHom.comp (continuousTransferCocycles H hH),
      continuousTransferCocycles_ker H hH⟩

/-- Corestriction evaluates on representatives by the constructed coset sum. -/
theorem continuousCorestrictionH2_class (c : C(H × H, M)) (hc : IsCocycle₂ c) :
    continuousCorestrictionH2 H hH (integralH2Class c hc) =
      integralH2Class (continuousTransferTwo H hH c)
        (continuousTransferTwo_isCocycle H hH c hc) :=
  AddMonoidHom.liftOfRightInverse_comp_apply
    (integralH2ClassHom (G := H) (M := M)) _ _
    ⟨integralH2ClassHom.comp (continuousTransferCocycles H hH),
      continuousTransferCocycles_ker H hH⟩ ⟨c, hc⟩

end LocalClassFieldTheory
