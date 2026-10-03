/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.UnramifiedOrderInflation

/-!
# Restriction to subgroups commutes with finite-stage order

These are ordinary group restrictions with the same coefficient order.
No change of base-field normalization or corestriction formula is asserted.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open IsLocalRing CategoryTheory HomologicalComplex groupCohomology

/-- Restriction of group arguments commutes with every coefficient morphism. -/
theorem coefficientRestriction_cochains {k G : Type} [CommRing k] [Group G]
    {A B : Rep k G} (φ : A ⟶ B) (H : Subgroup G) :
    cochainsMap (A := A) H.subtype (𝟙 (Rep.res H.subtype A)) ≫
        cochainsMap (A := Rep.res H.subtype A) (MonoidHom.id H)
          ((Rep.resFunctor H.subtype).map φ) =
      cochainsMap (A := A) (MonoidHom.id G) φ ≫
        cochainsMap (A := B) H.subtype (𝟙 (Rep.res H.subtype B)) := rfl

/-- The same coefficient square commutes after passing to group cohomology. -/
theorem coefficientRestriction_cohomology {k G : Type} [CommRing k] [Group G]
    {A B : Rep k G} (φ : A ⟶ B) (H : Subgroup G) (i : ℕ) :
    groupCohomology.map (A := A) H.subtype (𝟙 (Rep.res H.subtype A)) i ≫
        groupCohomology.map (A := Rep.res H.subtype A) (MonoidHom.id H)
          ((Rep.resFunctor H.subtype).map φ) i =
      groupCohomology.map (A := A) (MonoidHom.id G) φ i ≫
        groupCohomology.map (A := B) H.subtype (𝟙 (Rep.res H.subtype B)) i := by
  exact (homologyMap_comp _ _ i).symm.trans
    ((congrArg (fun f => homologyMap f i) (coefficientRestriction_cochains φ H)).trans
      (homologyMap_comp _ _ i))

variable (R K C : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field C] [Algebra K C] [Algebra R C] [IsScalarTower R K C]
  [Algebra.IsSeparable K C] [Finite (ResidueField R)] [IsSepClosed C]
  [IsAdicComplete (maximalIdeal R) R]

local notation "E[" n "]" => unramifiedFiniteStage R K C n
local notation "S[" n "]" => integralClosure R (E[n])

attribute [local instance] stageDvr stageFractionRing stageUnramified stageFinite stageLocalHom

variable (n : UnramifiedIndex)
  (H : Subgroup (unramifiedFiniteStage R K C n ≃ₐ[K] unramifiedFiniteStage R K C n))

/-- The canonical finite-stage order commutes with subgroup restriction on cochains. -/
abbrev unramifiedOrderRestrictionCochains :=
  coefficientRestriction_cochains (unramifiedOrderMap R (S[n]) K (E[n])) H

/-- The canonical finite-stage order commutes with subgroup restriction on cohomology. -/
abbrev unramifiedOrderRestrictionCohomology (i : ℕ) :=
  coefficientRestriction_cohomology (unramifiedOrderMap R (S[n]) K (E[n])) H i

end LocalClassFieldTheory
