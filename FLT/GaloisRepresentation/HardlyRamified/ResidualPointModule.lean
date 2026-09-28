/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.CategoryD
public import FLT.GaloisRepresentation.HardlyRamified.InertiaTwoSquareZero
public import FLT.GaloisRepresentation.HardlyRamified.ResidualCharacteristic
public import Mathlib.FieldTheory.Finite.Basic
public import FLT.Mathlib.Topology.Algebra.Module.ModuleTopology

/-!
# The finite point module of a residual representation

A finite coefficient representation gives a finite continuous Galois module.
Its three-primary order and square-zero inertia put every integral model in category D.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion

open scoped TensorProduct

namespace ThreeAdicPlan

local notation "Γ" => AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ

variable {k : Type*} [Field k] [Finite k] [TopologicalSpace k] [DiscreteTopology k]
    {V : Type} [AddCommGroup V] [Module k V] [Module.Finite k V]

/-- The scalar structure on the point-space synonym is the original coefficient action. -/
instance residualSpaceModule (ρ : GaloisRep ℚ k V) : Module k ρ.Space :=
  inferInstanceAs (Module k V)

/-- The point-space synonym has the same finite rank over its coefficient field. -/
instance residualSpaceModuleFinite (ρ : GaloisRep ℚ k V) : Module.Finite k ρ.Space :=
  inferInstanceAs (Module.Finite k V)

/-- Coefficient scalars commute with the action on the point-space synonym. -/
instance residualSpaceSMulComm (ρ : GaloisRep ℚ k V) : SMulCommClass Γ k ρ.Space where
  smul_comm σ a x := (ρ σ).map_smul a x

/-- The full finite Galois module of a residual representation. -/
def residualPointModule (ρ : GaloisRep ℚ k V) : FiniteContinuousGaloisModule := by
  let instFiniteV : Finite V := Module.finite_of_finite k
  let instFiniteSpace : Finite ρ.Space := instFiniteV
  letI instTopologyV : TopologicalSpace V := moduleTopology k V
  let instT2V : T2Space V := IsModuleTopology.t2Space k
  letI instTopologyEnd : TopologicalSpace (Module.End k V) := moduleTopology k _
  refine { Carrier := ρ.Space, continuous := ⟨fun x y ↦ ?_⟩ }
  change IsOpen {σ : Γ | ρ σ x = y}
  exact (isOpen_discrete ({y} : Set V)).preimage
    ((IsModuleTopology.continuous_of_linearMap
      (LinearMap.applyₗ (R := k) (M := V) (M₂ := V) x)).comp ρ.continuous)

/-- The coefficient structure survives bundling as a finite point module. -/
instance residualPointModuleModule (ρ : GaloisRep ℚ k V) :
    Module k (residualPointModule ρ) := residualSpaceModule ρ

/-- The bundled point module is finite dimensional over the original coefficient field. -/
instance residualPointModuleFinite (ρ : GaloisRep ℚ k V) :
    Module.Finite k (residualPointModule ρ) := residualSpaceModuleFinite ρ

/-- Galois and coefficient scalars commute on the bundled point module. -/
instance residualPointModuleSMulComm (ρ : GaloisRep ℚ k V) :
    SMulCommClass Γ k (residualPointModule ρ) := residualSpaceSMulComm ρ

/-- Every point is killed by three when the finite coefficient field is three-adic. -/
theorem residualPointModule_killed [Algebra ℤ_[3] k] (ρ : GaloisRep ℚ k V)
    (M : ModelOverZInvTwo (residualPointModule ρ)) :
    KilledByQ 3 (FiniteFlatObject.ofModel M) := by
  let instCharThree : CharP k 3 := charP_three_of_finite_padic_algebra k
  have hk (x : V) : (3 : ℕ) • x = 0 := by
    rw [← Nat.cast_smul_eq_nsmul k, CharP.cast_eq_zero k 3, zero_smul]
  exact hk

/-- Every integral model of a rank-two hardly ramified residual representation lies in D. -/
theorem residualPointModule_inCategoryD [Algebra ℤ_[3] k]
    (hV : Module.rank k V = 2) (ρ : GaloisRep ℚ k V)
    (hρ : GaloisRepresentation.IsHardlyRamified (show Odd 3 by decide) hV ρ)
    (M : ModelOverZInvTwo (residualPointModule ρ)) :
    InCategoryD (FiniteFlatObject.ofModel M) := by
  let instCharThree : CharP k 3 := charP_three_of_finite_padic_algebra k
  constructor
  · let instFintypeK : Fintype k := Fintype.ofFinite k
    obtain ⟨n, _, hn⟩ := FiniteField.card k 3
    refine ⟨(n : ℕ) * Module.finrank k V, ?_⟩
    change Nat.card V = _
    rw [Module.natCard_eq_pow_finrank (K := k), Nat.card_eq_fintype_card, hn, pow_mul]
  · intro σ hσ x
    exact congrArg (fun f : Module.End k V ↦ f x)
      (hardlyRamified_inertiaTwo_sq_zero hV ρ hρ σ hσ)

/-- The full point module inherits the unramified-outside condition from HR. -/
theorem residualPointModule_unramified [Algebra ℤ_[3] k]
    (hV : Module.rank k V = 2) (ρ : GaloisRep ℚ k V)
    (hρ : GaloisRepresentation.IsHardlyRamified (show Odd 3 by decide) hV ρ) :
    UnramifiedOutside {2, 3} (residualPointModule ρ) := by
  constructor
  intro p hp hpS σ hσ x
  let instUnramified := hρ.isUnramified p hp (by simpa using hpS)
  have he := GaloisRep.IsUnramifiedAt.localInertiaGroup_le (ρ := ρ) hσ
  change ρ (Field.absoluteGaloisGroup.map _ σ) x = x
  convert congrArg (fun f : Module.End k V ↦ f x) he using 1
  change ρ (Field.absoluteGaloisGroup.map _ σ) x =
    ρ (Field.absoluteGaloisGroup.map _ σ) x
  congr 4
  exact Subsingleton.elim _ _

/-- Flatness over a discrete coefficient field supplies a model of the full local action. -/
theorem residualPointModule_localModel
    (ρ : GaloisRep ℚ k V)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (hflat : ρ.IsFlatAt v) :
    Nonempty (HasFiniteFlatModel (v.adicCompletionIntegers ℚ)
      ((residualPointModule ρ).restrict (algebraMap ℚ (v.adicCompletion ℚ)))) := by
  let e : (k ⧸ (⊥ : Ideal k)) ⊗[k] V ≃ₗ[k] V :=
    (TensorProduct.congr (AlgEquiv.quotientBot k k).toLinearEquiv
      (LinearEquiv.refl k V)).trans (TensorProduct.lid k V)
  let q : ((ρ.baseChange (k ⧸ (⊥ : Ideal k))).toLocal v).Space →+[
      Field.absoluteGaloisGroup (v.adicCompletion ℚ)]
      ((residualPointModule ρ).restrict (algebraMap ℚ (v.adicCompletion ℚ))) :=
    { e.toAddMonoidHom with
      map_smul' := by
        intro σ x
        change e (((ρ.baseChange (k ⧸ (⊥ : Ideal k))).toLocal v) σ x) =
          (ρ.toLocal v) σ (e x)
        induction x using TensorProduct.inductionOn with
        | tmul a x => simp [e, GaloisRep.baseChange_map, GaloisRep.baseChange_tmul]
        | add x y hx hy => simp_all }
  apply (nonempty_hasFiniteFlatModel_iff _).mpr
  exact (hflat.cond ⊥ (isOpen_discrete _)).map _ _ _ _ q e.bijective

end ThreeAdicPlan
