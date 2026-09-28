/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.GroupScheme.FiniteFlatDifferentials
public import FLT.GroupScheme.PadicPatchingRings
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.RingTheory.Kaehler.TensorProduct
public import Mathlib.RingTheory.Smooth.Fiber

/-!
# Detecting étaleness of three-torsion models at three

For a module over `ℤ[1/2]` killed by three, scalar extension to `ℤ₃` is
injective: reduction modulo three extends its scalar action to `ℤ₃` and
provides a retraction. Applied to Kähler differentials, this detects global
étaleness of a model killed by three from its three-adic base change.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace ThreeAdicPlan

local instance : Fact (¬ ((3 : ℕ) : ℤ) ∣ (2 : ℤ)) := ⟨by decide⟩
local instance : Algebra ZInvTwo ℤ_[3] := (PadicPatching.baseToLocal 3 2).toAlgebra

/-- Scalar extension to the three-adic integers detects elements of a module
killed by three over the integers with two inverted. -/
theorem threeTorsion_tensor_injective (M : Type) [AddCommGroup M] [Module ZInvTwo M]
    (h3 : ∀ x : M, (3 : ℕ) • x = 0) :
    Function.Injective (fun x : M ↦ (1 : ℤ_[3]) ⊗ₜ[ZInvTwo] x) := by
  let : Module (ZMod 3) M := AddCommGroup.zmodModule h3
  let : Module ℤ_[3] M := Module.compHom M (PadicInt.toZMod : ℤ_[3] →+* ZMod 3)
  have h : (Module.toAddMonoidEnd ℤ_[3] M).comp (algebraMap ZInvTwo ℤ_[3]) =
      Module.toAddMonoidEnd ZInvTwo M := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (2 : ℤ))
    exact Subsingleton.elim _ _
  let : IsScalarTower ZInvTwo ℤ_[3] M :=
    IsScalarTower.of_algebraMap_smul fun r x ↦ DFunLike.congr_fun (DFunLike.congr_fun h r) x
  let f : ℤ_[3] ⊗[ZInvTwo] M →ₗ[ℤ_[3]] M :=
    (LinearMap.id : M →ₗ[ZInvTwo] M).liftBaseChange ℤ_[3]
  intro x y hxy
  have := congrArg f hxy
  simpa [f] using this

/-- A finite-flat model killed by three is étale if its three-adic scalar extension
is étale. The differential annihilation controls all other primes automatically. -/
theorem FF.etale_of_etale_threeAdic_baseChange (H : FF ZInvTwo ℚ)
    (h3 : KilledBy 3 H)
    [Algebra.Etale ℤ_[3] (ℤ_[3] ⊗[ZInvTwo] H.CoordinateRing)] :
    Algebra.Etale ZInvTwo H.CoordinateRing := by
  let A := H.CoordinateRing
  let B := ℤ_[3] ⊗[ZInvTwo] A
  let : Algebra A B := Algebra.TensorProduct.rightAlgebra
  let e := KaehlerDifferential.tensorKaehlerEquivBase ZInvTwo ℤ_[3] A B
  have hi := threeTorsion_tensor_injective (KaehlerDifferential ZInvTwo A)
    (H.nsmul_kaehlerDifferential_eq_zero 3 h3)
  let : Algebra.FormallyUnramified ZInvTwo A := ⟨⟨fun x y ↦ hi (e.injective
    (Subsingleton.elim _ _))⟩⟩
  let : Algebra.FinitePresentation ZInvTwo A :=
    (Algebra.FinitePresentation.of_finiteType (R := ZInvTwo) (A := A)).mp inferInstance
  exact Algebra.Etale.of_formallyUnramified_of_flat

end ThreeAdicPlan
