/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.UnramifiedDiagram

/-!
# Reindexing the unramified Galois limit by degree

The final stage functor becomes initial on opposite categories. Whiskering
Mathlib's explicit limit cone therefore gives the same profinite group.
The comparison's coordinates are the original finite restriction maps.
-/

@[expose] public noncomputable section

universe u

namespace LocalClassFieldTheory

open IsLocalRing CategoryTheory CategoryTheory.Limits

variable (R K C : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field C] [Algebra K C] [Algebra R C] [IsScalarTower R K C]
  [Algebra.IsSeparable K C] [Finite (ResidueField R)] [IsSepClosed C]
  [IsAdicComplete (maximalIdeal R) R]

/-- The explicit profinite limits before and after degree reindexing are isomorphic. -/
def unramifiedDegreeLimitIso :
    ProfiniteGrp.limit
        (InfiniteGalois.asProfiniteGaloisGroupFunctor K (maximalUnramified R K C)) ≅
      ProfiniteGrp.limit (unramifiedDegreeDiagram R K C) :=
  ((Functor.Initial.isLimitWhiskerEquiv (unramifiedStageFunctor R K C).op
    (ProfiniteGrp.limitCone
      (InfiniteGalois.asProfiniteGaloisGroupFunctor K (maximalUnramified R K C)))).symm
    (ProfiniteGrp.limitConeIsLimit _)).conePointUniqueUpToIso
      (ProfiniteGrp.limitConeIsLimit _)

/-- An isomorphism of profinite groups preserves their group structures and topologies. -/
def profiniteIsoContinuousMulEquiv {X Y : ProfiniteGrp} (e : X ≅ Y) : X ≃ₜ* Y where
  toFun := e.hom
  invFun := e.inv
  left_inv := fun x => ConcreteCategory.congr_hom e.hom_inv_id x
  right_inv := fun x => ConcreteCategory.congr_hom e.inv_hom_id x
  map_mul' := map_mul e.hom.hom
  continuous_toFun := e.hom.hom.continuous
  continuous_invFun := e.inv.hom.continuous

/-- The reindexed limit is topologically and multiplicatively the Galois group of the union. -/
def unramifiedDegreeLimitEquiv :
    Gal(maximalUnramified R K C/K) ≃ₜ*
      ↥(ProfiniteGrp.limit (unramifiedDegreeDiagram R K C)) :=
  (unramifiedGaloisLimitEquiv R K C).trans
    (profiniteIsoContinuousMulEquiv (unramifiedDegreeLimitIso R K C))

/-- At each positive degree the comparison is ordinary restriction to that finite stage. -/
theorem unramifiedDegreeLimitEquiv_apply (σ : Gal(maximalUnramified R K C/K))
    (n : UnramifiedIndex) :
    (unramifiedDegreeLimitEquiv R K C σ).val (Opposite.op n) =
      σ.restrictNormal (unramifiedFiniteStage R K C n) := by
  have h := IsLimit.conePointUniqueUpToIso_hom_comp
    ((Functor.Initial.isLimitWhiskerEquiv (unramifiedStageFunctor R K C).op
    (ProfiniteGrp.limitCone
      (InfiniteGalois.asProfiniteGaloisGroupFunctor K (maximalUnramified R K C)))).symm
      (ProfiniteGrp.limitConeIsLimit _))
    (ProfiniteGrp.limitConeIsLimit (unramifiedDegreeDiagram R K C)) (Opposite.op n)
  exact ConcreteCategory.congr_hom h (unramifiedGaloisLimitEquiv R K C σ)

end LocalClassFieldTheory
