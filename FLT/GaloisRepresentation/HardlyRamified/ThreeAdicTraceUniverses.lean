/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.ThreeAdicTraceProved
public import FLT.GaloisRepresentation.HardlyRamified.CoordinateChange
public import FLT.GaloisRepresentation.HardlyRamified.BaseChangeUniverses
public import FLT.GaloisRepresentation.HardlyRamified.FlatCoefficientQuotientUniverses
public import Mathlib.Algebra.Algebra.Shrink
public import Mathlib.RingTheory.Finiteness.Small

/-! # Original three-adic traces in independent coefficient and module universes

A finite coefficient algebra has a small copy. Scalar extension to that
isomorphic copy and a finite basis put the representation in the universes
of the proved sorting theorem. Injectivity then descends its trace identity.
-/

@[expose] public noncomputable section
attribute [local instance 2000] Algebra.toSMul Algebra.toModule
open scoped TensorProduct
namespace GaloisRepresentation.IsHardlyRamified
variable {R V : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
  [Algebra ℤ_[3] R] [Module.Free ℤ_[3] R] [Module.Finite ℤ_[3] R]
  [TopologicalSpace R] [IsTopologicalRing R] [IsModuleTopology ℤ_[3] R]
  [AddCommGroup V] [Module R V] [Module.Finite R V] [Module.Free R V]
  (hV : Module.rank R V = 2) {ρ : GaloisRep ℚ R V}

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The sorted-input trace theorem holds for the original independent universes. -/
theorem trace_eq_one_add_det_three_universes
    (hρ : IsHardlyRamified (by decide : Odd 3) hV ρ)
    (g : Field.absoluteGaloisGroup ℚ) :
    LinearMap.trace R V (ρ g) = 1 + LinearMap.det (ρ g) := by
  let : Small.{0} R := Module.Finite.small ℤ_[3] R
  let S := Shrink.{0} R
  let e : R ≃ₐ[ℤ_[3]] S := (Shrink.algEquiv ℤ_[3] R).symm
  let : Algebra R S := e.toRingHom.toAlgebra
  let : IsScalarTower ℤ_[3] R S :=
    IsScalarTower.of_algebraMap_eq' (R := ℤ_[3]) (S := R) (A := S) (by
    apply RingHom.ext
    intro a
    exact (e.commutes a).symm)
  let : Module.Finite ℤ_[3] S := Module.Finite.equiv e.toLinearEquiv
  let : Module.Free ℤ_[3] S := Module.Free.of_equiv e.toLinearEquiv
  let : IsLocalRing S := e.toRingEquiv.isLocalRing
  let : TopologicalSpace S := moduleTopology ℤ_[3] S
  let : IsTopologicalRing S := IsModuleTopology.isTopologicalRing ℤ_[3] S
  let : ContinuousSMul R S := continuousSMul_of_algebraMap R S
    (IsModuleTopology.continuous_of_linearMap e.toLinearMap)
  have hVS : Module.rank S (S ⊗[R] V) = 2 := by
    simpa [Module.rank_baseChange] using hV
  have hσ := ThreeAdicPlan.hardlyRamified_baseChange_of_flat_universes
    (by decide : Odd 3) hV hVS hρ
    (ThreeAdicPlan.flatAt_quotient_universes e.surjective ρ _ hρ.isFlat)
  have hfin : Module.finrank S (S ⊗[R] V) = 2 := Module.finrank_eq_of_rank_eq hVS
  let b := (Module.finBasisOfFinrankEq S (S ⊗[R] V) hfin).equivFun
  have hW : Module.rank S (Fin 2 → S) = 2 := by simp
  have ht := trace_eq_one_add_det_three hW
    (hσ.conj (by decide : Odd 3) hVS hW b) g
  change LinearMap.trace S _ (b.conj ((ρ g).baseChange S)) =
    1 + LinearMap.det (b.conj ((ρ g).baseChange S)) at ht
  have hd : (b.conj ((ρ g).baseChange S)).det = ((ρ g).baseChange S).det :=
    by simpa only [LinearEquiv.conj_apply, LinearMap.comp_assoc] using
      LinearMap.det_conj ((ρ g).baseChange S) b
  rw [LinearMap.trace_conj', hd, LinearMap.trace_baseChange, LinearMap.det_baseChange] at ht
  have hi : Function.Injective (algebraMap R S) := e.injective
  apply hi
  simpa only [map_add, map_one] using ht

end GaloisRepresentation.IsHardlyRamified
