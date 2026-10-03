/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.ContinuousCorestrictionH2
public import FLT.LocalClassFieldTheory.ContinuousInflationH2

/-!
# Corestriction after restriction is multiplication by the index

The explicit continuous homotopy proves this identity for the actual
categorical H2 restriction map and the coset-sum corestriction.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open CategoryTheory HomologicalComplex groupCohomology

variable {G M : Type} [Group G] [AddCommGroup M] [DistribMulAction G M]
  [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul G M] (H : Subgroup G) [CompactSpace H]
  [Fintype (G ⧸ H)] (hH : IsOpen (H : Set G))

/-- Restriction to a subgroup uses the identity coefficient map. -/
def subgroupRestrictionCoefficients :
    Rep.res H.subtype (Rep.of (Representation.ofDistribMulAction ℤ G M)) ⟶
      Rep.of (Representation.ofDistribMulAction ℤ H M) :=
  Rep.ofHom ⟨LinearMap.id, fun _ => rfl⟩

/-- Actual restriction on continuous H2 to the subgroup. -/
def subgroupRestrictionH2 : continuousCohomology ℤ G M 2 →+
    continuousCohomology ℤ H M 2 :=
  (homologyMap (continuousRestriction H.subtype continuous_subtype_val
    (subgroupRestrictionCoefficients (M := M) H)) 2).hom.toAddMonoidHom

/-- The coset-sum transfer composed with actual restriction multiplies by the index. -/
theorem continuousCorestrictionH2_restriction (x : continuousCohomology ℤ G M 2) :
    continuousCorestrictionH2 H hH (subgroupRestrictionH2 H x) =
      Fintype.card (G ⧸ H) • x := by
  obtain ⟨c, hc, rfl⟩ := integralH2Class_surjective x
  change continuousCorestrictionH2 H hH
    ((homologyMap (continuousRestriction H.subtype continuous_subtype_val
      (subgroupRestrictionCoefficients H)) 2).hom (integralH2Class c hc)) = _
  rw [continuousInflationH2_class, continuousCorestrictionH2_class]
  let z : continuousTwoCocycles (G := G) (M := M) := ⟨c, hc⟩
  change _ = Fintype.card (G ⧸ H) • integralH2ClassHom z
  rw [← map_nsmul]
  apply (integralH2Class_eq_iff _ _ _ (Fintype.card (G ⧸ H) • z).property).mpr
  refine ⟨continuousTransferRestrictionHomotopy H hH c, fun g h => ?_⟩
  change g • continuousTransferRestrictionHomotopy H hH c h -
    continuousTransferRestrictionHomotopy H hH c (g * h) +
    continuousTransferRestrictionHomotopy H hH c g =
    transferTwo H (fun p => c (p.1, p.2)) (g, h) - Fintype.card (G ⧸ H) • c (g, h)
  rw [continuousTransferTwo_restriction H hH c hc]
  abel

end LocalClassFieldTheory
