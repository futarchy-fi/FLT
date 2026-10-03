/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.UnramifiedStageOrderMaps
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

/-!
# Finite-stage inflation commutes with order

Restriction of Galois groups and inclusion of field units give the actual
inflation maps. The canonical tower-order theorem proves their cochain and
cohomology squares with constant integer coefficients.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open IsLocalRing CategoryTheory HomologicalComplex groupCohomology

variable (R K C : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field C] [Algebra K C] [Algebra R C] [IsScalarTower R K C]
  [Algebra.IsSeparable K C] [Finite (ResidueField R)] [IsSepClosed C]
  [IsAdicComplete (maximalIdeal R) R]

local notation "E[" n "]" => unramifiedFiniteStage R K C n
local notation "S[" n "]" => integralClosure R (E[n])

attribute [local instance] stageDvr stageFractionRing stageUnramified stageFinite stageLocalHom

variable {n m : UnramifiedIndex} (h : n ≤ m)

/-- Restriction in the existing degree-indexed Galois diagram. -/
def unramifiedStageRestriction : Gal(E[m]/K) →* Gal(E[n]/K) :=
  ((unramifiedDegreeDiagram R K C).map (homOfLE h).op).hom.toMonoidHom

/-- The finite-stage unit inclusion intertwines restriction of automorphisms. -/
theorem unramifiedStageUnitMap_equivariant (g : Gal(E[m]/K)) (x : (E[n])ˣ) :
    unramifiedStageUnitMap R K C h
        (Units.map (unramifiedStageRestriction R K C h g).toMonoidHom x) =
      Units.map g.toMonoidHom (unramifiedStageUnitMap R K C h x) := by
  let : Algebra (E[n]) (E[m]) :=
    (Subsemiring.inclusion (unramifiedFiniteStage_monotone R K C h)).toAlgebra
  let : IsScalarTower K (E[n]) (E[m]) := IsScalarTower.of_algebraMap_eq' rfl
  apply Units.ext
  exact g.restrictNormal_commutes (E[n]) (x : E[n])

/-- The multiplicative coefficient arrow for inflation. -/
def unramifiedStageUnitInflation :
    Rep.res (unramifiedStageRestriction R K C h) (Rep.ofAlgebraAutOnUnits K (E[n])) ⟶
      Rep.ofAlgebraAutOnUnits K (E[m]) :=
  Rep.ofHom ⟨(unramifiedStageUnitMap R K C h).toAdditive.toIntLinearMap, fun g => by
    apply LinearMap.ext
    intro x
    exact unramifiedStageUnitMap_equivariant R K C h g x.toMul⟩

/-- Constant integers inflate by the identity coefficient map. -/
def unramifiedStageIntegerInflation :
    Rep.res (unramifiedStageRestriction R K C h) (Rep.trivial ℤ Gal(E[n]/K) ℤ) ⟶
      Rep.trivial ℤ Gal(E[m]/K) ℤ := Rep.ofHom ⟨LinearMap.id, fun _ => rfl⟩

/-- The actual finite-stage cochain inflation commutes with normalized order. -/
theorem unramifiedOrderInflation_cochains :
    cochainsMap (unramifiedStageRestriction R K C h) (unramifiedStageUnitInflation R K C h) ≫
        cochainsMap (MonoidHom.id _) (unramifiedOrderMap R (S[m]) K (E[m])) =
      cochainsMap (MonoidHom.id _) (unramifiedOrderMap R (S[n]) K (E[n])) ≫
        cochainsMap (unramifiedStageRestriction R K C h)
          (unramifiedStageIntegerInflation R K C h) := by
  ext i c t
  exact congrArg Multiplicative.toAdd (unramifiedStageOrder_natural R K C h
    (Additive.toMul (c (unramifiedStageRestriction R K C h ∘ t))))

/-- The induced finite-stage cohomology inflation has the same order square. -/
theorem unramifiedOrderInflation_cohomology (i : ℕ) :
    groupCohomology.map (unramifiedStageRestriction R K C h)
        (unramifiedStageUnitInflation R K C h) i ≫
        groupCohomology.map (MonoidHom.id _) (unramifiedOrderMap R (S[m]) K (E[m])) i =
      groupCohomology.map (MonoidHom.id _) (unramifiedOrderMap R (S[n]) K (E[n])) i ≫
        groupCohomology.map (unramifiedStageRestriction R K C h)
          (unramifiedStageIntegerInflation R K C h) i := by
  exact (homologyMap_comp _ _ i).symm.trans
    ((congrArg (fun f => homologyMap f i) (unramifiedOrderInflation_cochains R K C h)).trans
      (homologyMap_comp _ _ i))

end LocalClassFieldTheory
