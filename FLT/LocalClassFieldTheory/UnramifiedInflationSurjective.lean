/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.FiniteRelativeSaturation
public import FLT.LocalClassFieldTheory.FiniteRelativeCocycleDescent
public import FLT.LocalClassFieldTheory.FiniteExtensionDvr

/-!
# Surjectivity of unramified inflation

Descend an absolute cocycle to a finite Galois fixed field, construct its
complete DVR, and apply finite relative saturation. Together with the proved
injection this gives bijectivity of the actual unramified inflation map.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open IsLocalRing CategoryTheory groupCohomology

variable (R K C : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field C] [Algebra K C] [Algebra R C] [IsScalarTower R K C]
  [Algebra.IsSeparable K C] [Finite (ResidueField R)] [IsSepClosed C] [CharZero C]
  [IsAdicComplete (maximalIdeal R) R]
  (p : ℕ) [Fact p.Prime] [CharP (ResidueField R) p]

attribute [local instance] unramifiedUnionGalois fieldUnitAction
  unramifiedFieldUnitTopology unramifiedFieldUnitDiscrete
  separableClosureGalois separableClosureUnitTopology separableClosureUnitDiscrete
  relativeBaseTower

include p in
/-- Every absolute multiplicative H² class is inflated from the unramified union. -/
theorem unramifiedMultiplicativeInflationH2_surjective :
    Function.Surjective (unramifiedMultiplicativeInflation R K C 2).hom := by
  intro x
  obtain ⟨c, hc, rfl⟩ := integralH2Class_surjective x
  obtain ⟨U, d, hd, he⟩ := finiteRelative_cocycle_descent K C c hc
  let E := IntermediateField.fixedField U.toSubgroup
  let : FiniteDimensional K E := galoisOpenStage_fixedField_finite K C U
  let : CharZero E := E.val.toRingHom.charZero
  let S := integralClosure R E
  let : Module.IsTorsionFree R E := .trans_faithfulSMul R K E
  let : Module.Finite R S := IsIntegralClosure.finite R K E S
  let : IsFractionRing S E := integralClosure.isFractionRing_of_finite_extension K E
  let : IsDiscreteValuationRing S := finiteExtension_dvr R K E
  let : IsAdicComplete (maximalIdeal S) S := finiteDvr_complete R S
  let : Finite (ResidueField S) := ResidueField.finite_of_finite (R := R) (S := S)
    inferInstance
  let : CharP (ResidueField S) p := charP_of_injective_ringHom
    (ResidueField.map (algebraMap R S)).injective p
  let : TopologicalSpace (Additive Eˣ) := ⊥
  let : DiscreteTopology (Additive Eˣ) := ⟨rfl⟩
  let dc : C(Gal(E/K) × Gal(E/K), Additive Eˣ) := ⟨d, continuous_of_discreteTopology⟩
  have hd' : IsCocycle₂ dc := hd
  obtain ⟨y, hy⟩ := finiteRelative_unramified_saturation R S K C E p
    (integralH2Class (k := ℤ) dc hd')
  refine ⟨y, hy.trans ?_⟩
  change (HomologicalComplex.homologyMap (continuousRestriction
    (AlgEquiv.restrictNormalHom E) (InfiniteGalois.restrictNormalHom_continuous E)
    (galoisInflationCoefficients K C E)) 2).hom (integralH2Class dc hd') = _
  rw [continuousInflationH2_class]
  congr 1
  apply ContinuousMap.ext
  intro z
  exact he z.1 z.2

include p in
/-- The actual unramified inflation is bijective in degree two. -/
theorem unramifiedMultiplicativeInflationH2_bijective :
    Function.Bijective (unramifiedMultiplicativeInflation R K C 2).hom :=
  ⟨unramifiedMultiplicativeInflationH2_injective R K C,
    unramifiedMultiplicativeInflationH2_surjective R K C p⟩

end LocalClassFieldTheory
