/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.UnramifiedDegreeLimit
public import FLT.LocalClassFieldTheory.UnramifiedIntegralModel

/-!
# Arithmetic Frobenius in the degree-indexed diagram

Each finite field uses its canonical integral closure. Its DVR and unramified
structures come from the constructed stage. The restriction arrows preserve
arithmetic Frobenius by the integral tower comparison.
-/

@[expose] public noncomputable section

universe u

namespace LocalClassFieldTheory

open IsLocalRing CategoryTheory

variable (R K C : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field C] [Algebra K C] [Algebra R C] [IsScalarTower R K C]
  [Algebra.IsSeparable K C] [Finite (ResidueField R)] [IsSepClosed C]
  [IsAdicComplete (maximalIdeal R) R]

/-- Reindexing a stage inside the union preserves its actual unramified model. -/
theorem unramifiedFiniteStage_isUnramified (n : UnramifiedIndex) :
    IsUnramifiedStage R K (unramifiedFiniteStage R K C n) :=
  (unramifiedStage_isUnramified R K C n.degree).of_algEquiv
    (IntermediateField.restrictAlgEquiv
      (unramifiedStage_le_maximalUnramified R K C n.degree))

local notation "E[" n "]" => unramifiedFiniteStage R K C n
local notation "S[" n "]" => integralClosure R (E[n])

local instance stageDvr (n : UnramifiedIndex) : IsDiscreteValuationRing (S[n]) :=
  (unramifiedFiniteStage_isUnramified R K C n).canonical_dvr

local instance stageUnramified (n : UnramifiedIndex) : Algebra.FormallyUnramified R (S[n]) :=
  (unramifiedFiniteStage_isUnramified R K C n).canonical_unramified

local instance stageFractionRing (n : UnramifiedIndex) : IsFractionRing (S[n]) (E[n]) :=
  integralClosure.isFractionRing_of_finite_extension K (E[n])

local instance stageFinite (n : UnramifiedIndex) : Module.Finite R (S[n]) :=
  IsIntegralClosure.finite R K (E[n]) (S[n])

local instance stageLocalHom (n : UnramifiedIndex) : IsLocalHom (algebraMap R (S[n])) :=
  (algebraMap_isIntegral_iff.mpr inferInstance).isLocalHom (by
    intro x y h
    apply IsFractionRing.injective R K
    apply (algebraMap K (E[n])).injective
    simpa only [← IsScalarTower.algebraMap_apply] using
      congrArg (algebraMap (S[n]) (E[n])) h)

/-- The arithmetic Frobenius coordinate at a positive degree. -/
def unramifiedStageFrobenius (n : UnramifiedIndex) : Gal(E[n]/K) :=
  arithmeticFrobenius R (S[n]) K (E[n])

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 600000 in
-- The two canonical integral closures carry several compatible scalar-tower instances.
set_option synthInstance.maxHeartbeats 100000 in
/-- Every transition in the degree diagram sends arithmetic Frobenius to Frobenius. -/
theorem unramifiedStageFrobenius_map {n m : UnramifiedIndexᵒᵖ} (f : n ⟶ m) :
    (unramifiedDegreeDiagram R K C).map f (unramifiedStageFrobenius R K C n.unop) =
      unramifiedStageFrobenius R K C m.unop := by
  let h := (unramifiedFiniteStage_monotone R K C) (leOfHom f.unop)
  let : Algebra (E[m.unop]) (E[n.unop]) :=
    (Subsemiring.inclusion h).toAlgebra
  let : IsScalarTower K (E[m.unop]) (E[n.unop]) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower R (E[m.unop]) (E[n.unop]) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let i := (IsScalarTower.toAlgHom R (E[m.unop]) (E[n.unop])).mapIntegralClosure
  let : Algebra (S[m.unop]) (S[n.unop]) := i.toRingHom.toAlgebra
  let : Algebra (S[m.unop]) (E[n.unop]) :=
    ((algebraMap (E[m.unop]) (E[n.unop])).comp (algebraMap (S[m.unop]) (E[m.unop]))).toAlgebra
  let : IsScalarTower (S[m.unop]) (E[m.unop]) (E[n.unop]) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower (S[m.unop]) (S[n.unop]) (E[n.unop]) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower R (S[m.unop]) (S[n.unop]) :=
    IsScalarTower.of_algebraMap_eq fun r => (i.commutes r).symm
  let : Algebra.IsIntegral (S[m.unop]) (S[n.unop]) :=
    ⟨fun x => (Algebra.IsIntegral.isIntegral (R := R) x).tower_top⟩
  let : IsLocalHom (algebraMap (S[m.unop]) (S[n.unop])) :=
    (algebraMap_isIntegral_iff.mpr inferInstance).isLocalHom (by
      intro x y hxy
      apply Subtype.ext
      apply (algebraMap (E[m.unop]) (E[n.unop])).injective
      exact congrArg Subtype.val hxy)
  exact arithmeticFrobenius_restrict R (S[m.unop]) (S[n.unop]) K (E[m.unop]) (E[n.unop])

/-- Arithmetic Frobenius defines a compatible point of the degree-indexed limit. -/
def unramifiedFrobeniusPoint : ProfiniteGrp.limit (unramifiedDegreeDiagram R K C) :=
  ⟨fun n => unramifiedStageFrobenius R K C n.unop,
    fun _ _ f => unramifiedStageFrobenius_map R K C f⟩

/-- The arithmetic Frobenius automorphism of the entire unramified union. -/
def unramifiedFrobenius : Gal(maximalUnramified R K C/K) :=
  (unramifiedDegreeLimitEquiv R K C).symm (unramifiedFrobeniusPoint R K C)

/-- The union Frobenius restricts to the W16 arithmetic Frobenius at every degree. -/
theorem unramifiedFrobenius_restrict (n : UnramifiedIndex) :
    (unramifiedFrobenius R K C).restrictNormal (E[n]) =
      unramifiedStageFrobenius R K C n := by
  rw [← unramifiedDegreeLimitEquiv_apply, unramifiedFrobenius,
    ContinuousMulEquiv.apply_symm_apply]
  rfl

end LocalClassFieldTheory
