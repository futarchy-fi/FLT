/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.Extensions.CocycleAction
public import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Finite quotient descent for continuous cocycles

The kernel of the affine action supplies the quotient. Both the coefficient
action and the cocycle descend, without assuming a descent witness. Finite
coefficients suffice; compactness of the source is not needed.
-/

@[expose] public section

namespace GaloisRepresentation.Extensions

variable {G M : Type*} [Group G] [AddCommGroup M] [DistribMulAction G M]
    (c : G → M) (hc : groupCohomology.IsCocycle₁ c)

/-- The cocycle on the quotient by the affine kernel. -/
def descendedCocycle (q : G ⧸ (cocycleAction c hc).ker) : M :=
  QuotientGroup.kerLift (cocycleAction c hc) q 0

/-- Inflation recovers the original cocycle. -/
@[simp] theorem descendedCocycle_mk (g : G) : descendedCocycle c hc ⟦g⟧ = c g := by
  exact cocycleAction_apply_zero c hc g

/-- The linear part of the descended affine permutation. -/
def descendedLinear (q : G ⧸ (cocycleAction c hc).ker) (x : M) : M :=
  QuotientGroup.kerLift (cocycleAction c hc) q x - descendedCocycle c hc q

/-- The linear part agrees with the original action on representatives. -/
@[simp] theorem descendedLinear_mk (g : G) (x : M) :
    descendedLinear c hc ⟦g⟧ x = g • x := by
  simp only [descendedLinear, descendedCocycle, QuotientGroup.kerLift_mk]
  simp [cocycleAction, cocyclePerm]

/-- The coefficient action on the quotient by the affine kernel. -/
@[instance_reducible] def descendedAction :
    DistribMulAction (G ⧸ (cocycleAction c hc).ker) M where
  smul := descendedLinear c hc
  one_smul x := by
    change descendedLinear c hc 1 x = x
    simp [descendedLinear, descendedCocycle]
  mul_smul q r x := by
    change descendedLinear c hc (q * r) x =
      descendedLinear c hc q (descendedLinear c hc r x)
    induction q using QuotientGroup.induction_on with | H g =>
      induction r using QuotientGroup.induction_on with | H h =>
        simp only [← QuotientGroup.mk_mul, descendedLinear_mk, mul_smul]
  smul_zero q := sub_self _
  smul_add q x y := by
    change descendedLinear c hc q (x + y) =
      descendedLinear c hc q x + descendedLinear c hc q y
    induction q using QuotientGroup.induction_on with | H g =>
      simp only [descendedLinear_mk, smul_add]

/-- Inflation also recovers the original coefficient action. -/
@[simp] theorem descendedAction_mk (g : G) (x : M) :
    letI := descendedAction c hc
    (⟦g⟧ : G ⧸ (cocycleAction c hc).ker) • x = g • x := by
  exact descendedLinear_mk c hc g x

/-- The descended function is a crossed homomorphism for the descended action. -/
theorem descendedCocycle_isCocycle :
    letI := descendedAction c hc
    groupCohomology.IsCocycle₁ (descendedCocycle c hc) := by
  let := descendedAction c hc
  intro q r
  induction q using QuotientGroup.induction_on with | H g =>
    induction r using QuotientGroup.induction_on with | H h =>
      change descendedCocycle c hc (↑g * ↑h) =
        descendedLinear c hc ↑g (descendedCocycle c hc ↑h) + descendedCocycle c hc ↑g
      simpa only [← QuotientGroup.mk_mul, descendedCocycle_mk, descendedLinear_mk] using hc g h

/-- Finite coefficients give a finite quotient even without source compactness. -/
theorem finite_cocycleAction_quotient [Finite M] :
    Finite (G ⧸ (cocycleAction c hc).ker) :=
  Finite.of_injective _ (QuotientGroup.kerLift_injective (cocycleAction c hc))

variable [TopologicalSpace G] [TopologicalSpace M] [DiscreteTopology M] [Finite M]

/-- The affine kernel is open: it is a finite intersection of open fibers. -/
theorem isOpen_cocycleAction_ker (hcont : Continuous c)
    (hact : ∀ x : M, Continuous (fun g : G ↦ g • x)) :
    IsOpen ((cocycleAction c hc).ker : Set G) := by
  have heq : ((cocycleAction c hc).ker : Set G) =
      c ⁻¹' {0} ∩ ⋂ x : M, {g : G | g • x = x} := by
    ext g
    change g ∈ (cocycleAction c hc).ker ↔ _
    rw [mem_cocycleAction_ker]
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iInter,
      Set.mem_ofPred_eq]
  rw [heq]
  exact (hcont.isOpen_preimage _ (isOpen_discrete _)).inter
    (isOpen_iInter_of_finite fun x ↦ (hact x).isOpen_preimage _ (isOpen_discrete {x}))

/-- An explicitly constructed open normal subgroup supporting finite descent. -/
def cocycleOpenNormal (hcont : Continuous c)
    (hact : ∀ x : M, Continuous (fun g : G ↦ g • x)) : OpenNormalSubgroup G where
  toSubgroup := (cocycleAction c hc).ker
  isOpen' := isOpen_cocycleAction_ker c hc hcont hact

/-- The descended cocycle is continuous for the quotient topology. -/
theorem continuous_descendedCocycle [SeparatelyContinuousMul G] (hcont : Continuous c)
    (hact : ∀ x : M, Continuous (fun g : G ↦ g • x)) :
    Continuous (descendedCocycle c hc) := by
  let : DiscreteTopology (G ⧸ (cocycleAction c hc).ker) :=
    QuotientGroup.discreteTopology (isOpen_cocycleAction_ker c hc hcont hact)
  exact continuous_of_discreteTopology

/-- Each orbit map of the descended coefficient action is continuous. -/
theorem continuous_descendedLinear [SeparatelyContinuousMul G] (hcont : Continuous c)
    (hact : ∀ x : M, Continuous (fun g : G ↦ g • x)) (x : M) :
    Continuous (fun q ↦ descendedLinear c hc q x) := by
  let : DiscreteTopology (G ⧸ (cocycleAction c hc).ker) :=
    QuotientGroup.discreteTopology (isOpen_cocycleAction_ker c hc hcont hact)
  exact continuous_of_discreteTopology

end GaloisRepresentation.Extensions
