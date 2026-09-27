/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.LocalInertia
public import FLT.Mathlib.RingTheory.Valuation.RootLifting
public import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
public import Mathlib.RingTheory.LocalRing.ResidueField.Instances

/-!
# The geometric residue field of a local algebraic closure

The canonical valuation ring of the local algebraic closure is integral over the
adic integer ring. Its residue field is therefore an algebraic closure of the base
residue field. The comparison below respects coefficient reduction and identifies
both fibers of an integral Weierstrass model.
-/

@[expose] public section

open IsLocalRing
namespace NumberField
variable {K : Type*} [Field K] [NumberField K]
variable (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
local notation "Kv" => v.adicCompletion K
local notation "O" => v.adicCompletionIntegers K
local notation "Ω" => AlgebraicClosure Kv
local notation "A" => localClosureValuation v

/-- The base adic integers act on their integral closure valuation ring. -/
noncomputable instance localClosureValuationAlgebra : Algebra O A :=
  inferInstanceAs (Algebra O (integralClosure O Ω))

/-- The inclusion of the integral closure respects the base integer algebra. -/
instance localClosureValuation_isScalarTower : IsScalarTower O A Ω :=
  .of_algebraMap_eq fun _ => rfl

/-- The local closure valuation ring is integral over the base adic integers. -/
instance localClosureValuation_isIntegral : Algebra.IsIntegral O A :=
  inferInstanceAs (Algebra.IsIntegral O (integralClosure O Ω))

/-- The base adic integers embed faithfully in the integral closure valuation ring. -/
instance localClosureValuation_faithfulSMul : FaithfulSMul O A := by
  apply (faithfulSMul_iff_algebraMap_injective O A).mpr
  intro x y h
  have he := congrArg (fun z : A => (z : Ω)) h
  exact (FaithfulSMul.algebraMap_injective O Ω) he

/-- The integral inclusion of the base integers is a local homomorphism. -/
instance localClosureValuation_isLocalHom : IsLocalHom (algebraMap O A) := inferInstance

/-- The residue field extension induced by the integral closure is integral. -/
instance localClosureValuation_residue_isIntegral :
    Algebra.IsIntegral (ResidueField O) (ResidueField A) := by
  have : Algebra.IsIntegral A (ResidueField A) :=
    Algebra.isIntegral_of_surjective residue_surjective
  have : Algebra.IsIntegral O (ResidueField A) := .trans A
  exact .tower_top O

/-- The geometric residue field is an algebraic closure of the adic residue field. -/
instance localClosureValuation_residue_isAlgClosure :
    IsAlgClosure (ResidueField O) (ResidueField A) := by
  exact ⟨inferInstance, inferInstance⟩

/-- Compare the geometric residue field with an algebraic closure of the adic residue field. -/
noncomputable def localClosureResidueEquiv :
    ResidueField A ≃ₐ[ResidueField O] AlgebraicClosure (ResidueField O) :=
  IsAlgClosure.equiv _ _ _
end NumberField

open ValuativeRel
namespace NumberField
attribute [local instance] completionValuativeRel
variable {K : Type*} [Field K] [NumberField K]
variable (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
local notation "Kv" => v.adicCompletion K
local notation "O" => v.adicCompletionIntegers K
local notation "Ω" => AlgebraicClosure Kv
local notation "A" => localClosureValuation v

/-- Identify the canonical and adic integer rings of the completion. -/
noncomputable def completionIntegerEquiv : 𝒪[Kv] ≃+* O :=
  RingEquiv.subringCongr (completion_integerRing_eq v)

/-- Compare the geometric residue field with an algebraic closure of the canonical residue field. -/
noncomputable def localClosureResidueCanonicalEquiv :
    ResidueField A ≃+* AlgebraicClosure (ResidueField 𝒪[Kv]) :=
  IsAlgClosure.equivOfEquiv _ _ (ResidueField.mapEquiv (completionIntegerEquiv v).symm)

/-- Map canonical integers into the valuation ring of the local algebraic closure. -/
noncomputable def localClosureIntegerMap : 𝒪[Kv] →+* A :=
  (algebraMap O A).comp (completionIntegerEquiv v).toRingHom

/-- The map of integer rings is the usual field inclusion on underlying elements. -/
theorem localClosureIntegerMap_coe (x : 𝒪[Kv]) :
    (localClosureIntegerMap v x : Ω) = algebraMap Kv Ω (x : Kv) := rfl

/-- The residue-field comparison respects reduction of base integral elements. -/
theorem localClosureResidueCanonicalEquiv_residue (x : 𝒪[Kv]) :
    localClosureResidueCanonicalEquiv v (residue A (localClosureIntegerMap v x)) =
      algebraMap (ResidueField 𝒪[Kv]) (AlgebraicClosure (ResidueField 𝒪[Kv]))
        (residue 𝒪[Kv] x) := by
  change localClosureResidueCanonicalEquiv v
    (algebraMap (ResidueField O) (ResidueField A) (residue O (completionIntegerEquiv v x))) = _
  rw [localClosureResidueCanonicalEquiv, IsAlgClosure.equivOfEquiv_algebraMap]
  congr 1

/-- The generic fiber after extending the integer ring is the usual field base change. -/
theorem localClosure_map_generic (W : WeierstrassCurve 𝒪[Kv]) :
    (W.map (localClosureIntegerMap v)).map (algebraMap A Ω) =
      (W.map (algebraMap 𝒪[Kv] Kv)).map (algebraMap Kv Ω) := by
  rw [WeierstrassCurve.map_map, WeierstrassCurve.map_map]
  congr 1

/-- The residue-field comparison identifies the two ways to reduce and extend coefficients. -/
theorem localClosure_map_special (W : WeierstrassCurve 𝒪[Kv]) :
    ((W.map (localClosureIntegerMap v)).map (residue A)).map
      (localClosureResidueCanonicalEquiv v).toRingHom =
    (W.map (residue 𝒪[Kv])).map
      (algebraMap (ResidueField 𝒪[Kv]) (AlgebraicClosure (ResidueField 𝒪[Kv]))) := by
  simp only [WeierstrassCurve.map_map]
  congr 1
  ext x
  exact localClosureResidueCanonicalEquiv_residue v x

attribute [local instance] completion_isNonarchimedeanLocalField

/-- The extended integral model has the geometric generic fiber of the original curve. -/
theorem localClosure_integralModel_generic (E : WeierstrassCurve Kv)
    [E.IsIntegral 𝒪[Kv]] :
    ((E.integralModel 𝒪[Kv]).map (localClosureIntegerMap v)).map (algebraMap A Ω) =
      E.map (algebraMap Kv Ω) := by
  rw [localClosure_map_generic]
  exact congrArg (fun W => W.map (algebraMap Kv Ω))
    (E.baseChange_integralModel_eq 𝒪[Kv])

/-- The extended integral model has the geometric special fiber used in the reduction definition. -/
theorem localClosure_integralModel_special (E : WeierstrassCurve Kv)
    [E.IsMinimal 𝒪[Kv]] :
    (((E.integralModel 𝒪[Kv]).map (localClosureIntegerMap v)).map (residue A)).map
      (localClosureResidueCanonicalEquiv v).toRingHom =
    (E.reduction 𝒪[Kv]).map
      (algebraMap (ResidueField 𝒪[Kv]) (AlgebraicClosure (ResidueField 𝒪[Kv]))) :=
  localClosure_map_special v (E.integralModel 𝒪[Kv])

end NumberField
