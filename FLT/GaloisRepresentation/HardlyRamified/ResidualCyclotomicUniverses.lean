/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.ResidualCyclotomicRestriction
public import FLT.GaloisRepresentation.HardlyRamified.CoordinateChange
public import FLT.GaloisRepresentation.HardlyRamified.BaseChangeUniverses
public import FLT.GaloisRepresentation.HardlyRamified.FlatCoefficientQuotientUniverses
public import FLT.Deformations.RepresentationTheory.EquivAbsoluteIrreducible
public import Mathlib.Algebra.Algebra.Shrink
public import Mathlib.Algebra.Field.Shrink

/-!
# Cyclotomic restriction in independent residual universes

A finite coefficient field has a constructed small copy. Base change followed
by a finite basis reduces to the proved arithmetic theorem. Cancellation of
iterated base change returns the conclusion in the original universes.
-/

@[expose] public noncomputable section
attribute [local instance 2000] Algebra.toSMul Algebra.toModule
open scoped TensorProduct
universe u
namespace GaloisRepresentation.IsHardlyRamified

set_option backward.isDefEq.respectTransparency false in
/-- The cyclotomic restriction theorem for the exact universes of `lifts`. -/
theorem residual_cyclotomic_restriction_absolute_universes
    {p : ℕ} [Fact p.Prime] (hpodd : Odd p)
    {k V : Type*} [Field k] [Finite k] [Algebra ℤ_[p] k]
    [TopologicalSpace k] [DiscreteTopology k]
    [AddCommGroup V] [Module k V] [Module.Finite k V] [Module.Free k V]
    (hV : Module.rank k V = 2) {ρ : GaloisRep ℚ k V}
    (hρ : IsHardlyRamified hpodd hV ρ) (hirr : ρ.IsIrreducible) :
    Representation.IsAbsolutelyIrreducible.{u}
      (ρ.toRepresentation.comp (CyclotomicQuadratic.character p).ker.subtype) := by
  let S := Shrink.{0} k
  let e : k ≃ₐ[ℤ_[p]] S := (Shrink.algEquiv.{0} ℤ_[p] k).symm
  let : Algebra k S := e.toRingHom.toAlgebra
  let : IsScalarTower ℤ_[p] k S :=
    IsScalarTower.of_algebraMap_eq' (R := ℤ_[p]) (S := k) (A := S) (by
      apply RingHom.ext
      intro a
      exact (e.commutes a).symm)
  let : TopologicalSpace S := ⊥
  let : DiscreteTopology S := ⟨rfl⟩
  let : ContinuousSMul k S := DiscreteTopology.instContinuousSMul k S
  have hVS : Module.rank S (S ⊗[k] V) = 2 := by
    rw [Module.rank_eq_ofNat_iff_finrank_eq_ofNat 2, Module.finrank_baseChange]
    exact Module.finrank_eq_of_rank_eq hV
  have hσ := ThreeAdicPlan.hardlyRamified_baseChange_of_flat_universes
    hpodd hV hVS hρ
    (ThreeAdicPlan.flatAt_quotient_universes e.surjective ρ _ hρ.isFlat)
  let b := (Module.finBasisOfFinrankEq S (S ⊗[k] V)
    (Module.finrank_eq_of_rank_eq hVS)).equivFun
  have hW : Module.rank S (Fin 2 → S) = 2 := by simp
  let τ := (ρ.baseChange S).conj b
  let eb : (ρ.baseChange S).toRepresentation.Equiv τ.toRepresentation :=
    .mk b (by
      intro g
      apply LinearMap.ext
      intro x
      change b ((ρ.baseChange S) g x) = b ((ρ.baseChange S) g (b.symm (b x)))
      rw [b.symm_apply_apply])
  have hiS := (isAbsolutelyIrreducible hpodd hV hρ hirr).absolutelyIrreducible S
    inferInstance inferInstance
  have hτ := residual_cyclotomic_restriction_absolute hpodd hW
    (hσ.conj hpodd hVS hW b) (eb.isIrreducible_iff.mp hiS)
  let H := (CyclotomicQuadratic.character p).ker
  let er : Representation.Equiv ((ρ.baseChange S).toRepresentation.comp H.subtype)
      (τ.toRepresentation.comp H.subtype) :=
    .mk b (by intro g; exact eb.toIntertwiningMap.isIntertwining' g.val)
  have hS := er.isAbsolutelyIrreducible_iff.mpr hτ
  constructor
  intro L _ _
  let : Algebra S L := ((algebraMap k L).comp e.symm.toRingHom).toAlgebra
  let : IsScalarTower k S L := IsScalarTower.of_algebraMap_eq' (R := k) (S := S) (A := L) (by
    apply RingHom.ext
    intro a
    exact congrArg (algebraMap k L) (e.symm_apply_apply a) |>.symm)
  exact (Representation.isIrreducible_baseChange_tower_iff
    (ρ.toRepresentation.comp H.subtype) S L).mp
      (hS.absolutelyIrreducible L inferInstance inferInstance)

end GaloisRepresentation.IsHardlyRamified
