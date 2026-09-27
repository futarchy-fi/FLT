/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.BialgebraBaseChange
public import FLT.GroupScheme.PadicHopfOperations

/-!
# Hopf identities for arithmetic patching

The descended operations satisfy the Hopf identities because they agree with the
away operations and the away maps on tensor powers are injective.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local instance 100000] CommRing.toCommSemiring CommSemiring.toSemiring
  Algebra.toSMul Algebra.toModule Subalgebra.toCommRing Subalgebra.toRing
  Ring.toAddCommGroup AddCommGroup.toAddGroup

open scoped TensorProduct

namespace ThreeAdicPlan.PadicPatching

variable (p : ℕ) [Fact p.Prime] (d : ℤ) [Fact (¬ (p : ℤ) ∣ d)]
    (A B : Type) [CommRing A] [CommRing B]
    [HopfAlgebra (Away d p) A] [HopfAlgebra ℤ_[p] B]
    [Algebra (Base d) A] [IsScalarTower (Base d) (Away d p) A]
    (e : ℚ_[p] ⊗[ℤ_[p]] B ≃ₐc[ℚ_[p]] ℚ_[p] ⊗[Away d p] A)

/-- Use the module inherited from the away Hopf algebra. -/
local instance : Module (Away d p) A := by exact Algebra.toModule

/-- Use the algebra module on the localization. -/
local instance : Module (Base d) (Away d p) := by exact Algebra.toModule

variable (P : ModulePatch p d A (localHopfLattice p d A B e).toSubmodule)

local notation "𝓡" => Base d
local notation "𝓢" => Away d p
local notation "L" => localHopfLattice p d A B e
local notation "H" => hopfIntersection p d A B e


/-- The integral tensor cube maps into the away tensor cube. -/
def hopfIntersectionTripleMap : H ⊗[𝓡] (H ⊗[𝓡] H) →ₐ[𝓡] A ⊗[𝓢] (A ⊗[𝓢] A) :=
  Algebra.TensorProduct.lift
    (((Algebra.TensorProduct.includeLeft : A →ₐ[𝓢] A ⊗[𝓢] (A ⊗[𝓢] A)).restrictScalars 𝓡).comp
      (hopfIntersection p d A B e).val)
    (((Algebra.TensorProduct.includeRight :
      (A ⊗[𝓢] A) →ₐ[𝓢] A ⊗[𝓢] (A ⊗[𝓢] A)).restrictScalars 𝓡).comp
      (algebraIntersectionTensorMap p d A L)) (fun _ _ ↦ Commute.all _ _)

/-- The triple-tensor map separates its first factor. -/
@[simp] theorem hopfIntersectionTripleMap_tmul (a : H) (z : H ⊗[𝓡] H) :
    hopfIntersectionTripleMap p d A B e (a ⊗ₜ[𝓡] z) =
      (a : A) ⊗ₜ[𝓢] algebraIntersectionTensorMap p d A L z := by
  simp [hopfIntersectionTripleMap]

include P in
/-- The integral tensor cube embeds in the away tensor cube. -/
theorem hopfIntersectionTripleMap_injective :
    Function.Injective (hopfIntersectionTripleMap p d A B e) := by
  let : NeZero d := ⟨denominator_ne_zero p d⟩
  have hi : Function.Injective (Algebra.ofId 𝓡 𝓢) := by
    apply IsLocalization.injective (M := Submonoid.powers (p : 𝓡)) 𝓢
    rintro x ⟨n, rfl⟩
    apply pow_mem
    apply mem_nonZeroDivisors_of_ne_zero
    intro hp
    have hq : (p : ℚ_[p]) = 0 := by simpa using congrArg (algebraMap 𝓡 ℚ_[p]) hp
    exact (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) hq
  let : FaithfulSMul 𝓡 𝓢 := (faithfulSMul_iff_algebraMap_injective 𝓡 𝓢).2 hi
  let : Module.Projective 𝓡 H := algebraIntersection_projective p d A L P
  let Q := algebraIntersectionModulePatch p d A L P
  let e1 : 𝓢 ⊗[𝓡] H ≃ₗ[𝓢] A := by exact Q.awayEquiv
  let e2 : 𝓢 ⊗[𝓡] (H ⊗[𝓡] H) ≃ₗ[𝓢] A ⊗[𝓢] A := by exact Q.tensorAwayEquiv
  let E := (TensorProduct.AlgebraTensorModule.distribBaseChange 𝓡 𝓢 H (H ⊗[𝓡] H)).trans
    (TensorProduct.congr e1 e2)
  have hE (z : H ⊗[𝓡] (H ⊗[𝓡] H)) :
      E (1 ⊗ₜ[𝓡] z) = hopfIntersectionTripleMap p d A B e z := by
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => simp [TensorProduct.tmul_add, hx, hy]
    | tmul x y =>
      simp only [E, LinearEquiv.trans_apply,
        TensorProduct.AlgebraTensorModule.distribBaseChange_tmul,
        TensorProduct.congr_tmul, hopfIntersectionTripleMap_tmul]
      have h1 : e1 (1 ⊗ₜ[𝓡] x) = x.val := by
        change algebraIntersectionAwayMap p d A L (1 ⊗ₜ[𝓡] x) = x.val
        exact (algebraIntersectionAwayMap_tmul p d A L 1 x).trans
          (one_smul (Away d p) (x : A))
      have h2 : e2 (1 ⊗ₜ[𝓡] y) = algebraIntersectionTensorMap p d A L y := by
        exact (algebraIntersectionTensorMap_eq p d A L P y).symm
      exact congrArg₂ (fun a b ↦ a ⊗ₜ[𝓢] b) h1 h2
  intro x y h
  apply Module.Flat.tensorProduct_mk_injective 𝓡 (H ⊗[𝓡] (H ⊗[𝓡] H)) 𝓢
  apply E.injective
  simpa only [TensorProduct.mk_apply, hE] using h

include P

omit P in
/-- The triple-tensor map respects reassociation. -/
theorem hopfIntersectionTripleMap_assoc_tmul (z : H ⊗[𝓡] H) (b : H) :
    hopfIntersectionTripleMap p d A B e (Algebra.TensorProduct.assoc 𝓡 𝓡 𝓡 H H H (z ⊗ₜ[𝓡] b)) =
      Algebra.TensorProduct.assoc 𝓢 𝓢 𝓢 A A A
        (algebraIntersectionTensorMap p d A L z ⊗ₜ[𝓢] (b : A)) := by
  induction z using TensorProduct.inductionOn with
  | tmul a c => simp
  | add x y hx hy => simp [TensorProduct.add_tmul, hx, hy]

/-- The triple-tensor map respects comultiplication on the right. -/
theorem hopfIntersectionTripleMap_rightComul (z : H ⊗[𝓡] H) :
    hopfIntersectionTripleMap p d A B e
      (Algebra.TensorProduct.map (AlgHom.id 𝓡 H) (hopfIntersectionComul p d A B e P) z) =
      Algebra.TensorProduct.map (AlgHom.id 𝓢 A) (Bialgebra.comulAlgHom 𝓢 A)
        (algebraIntersectionTensorMap p d A L z) := by
  induction z using TensorProduct.inductionOn with
  | tmul a b => simp [hopfIntersectionComul_map]
  | add x y hx hy => simp [hx, hy]

/-- The triple-tensor map respects comultiplication on the left. -/
theorem hopfIntersectionTripleMap_leftComul (z : H ⊗[𝓡] H) :
    hopfIntersectionTripleMap p d A B e (Algebra.TensorProduct.assoc 𝓡 𝓡 𝓡 H H H
      (Algebra.TensorProduct.map (hopfIntersectionComul p d A B e P) (AlgHom.id 𝓡 H) z)) =
      Algebra.TensorProduct.assoc 𝓢 𝓢 𝓢 A A A
        (Algebra.TensorProduct.map (Bialgebra.comulAlgHom 𝓢 A) (AlgHom.id 𝓢 A)
          (algebraIntersectionTensorMap p d A L z)) := by
  induction z using TensorProduct.inductionOn with
  | tmul a b => simp [hopfIntersectionTripleMap_assoc_tmul, hopfIntersectionComul_map]
  | add x y hx hy => simp [hx, hy]

/-- Coassociativity descends along the injective triple-tensor map. -/
theorem hopfIntersectionComul_coassoc :
    (Algebra.TensorProduct.assoc 𝓡 𝓡 𝓡 H H H).toAlgHom.comp
      ((Algebra.TensorProduct.map (hopfIntersectionComul p d A B e P) (.id 𝓡 H)).comp
        (hopfIntersectionComul p d A B e P)) =
      (Algebra.TensorProduct.map (.id 𝓡 H) (hopfIntersectionComul p d A B e P)).comp
        (hopfIntersectionComul p d A B e P) := by
  ext a
  apply hopfIntersectionTripleMap_injective p d A B e P
  simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    hopfIntersectionTripleMap_leftComul, hopfIntersectionTripleMap_rightComul,
    hopfIntersectionComul_map]
  exact Coalgebra.coassoc_apply (R := 𝓢) (a : A)

local notation "ε" => hopfIntersectionCounit p d A B e

omit P in
/-- The left integral counit agrees with its generic counterpart. -/
theorem hopfIntersectionCounit_leftTensor (z : H ⊗[𝓡] H) :
    ((Algebra.TensorProduct.lid 𝓡 H)
      (Algebra.TensorProduct.map ε (AlgHom.id 𝓡 H) z) : A) =
    Algebra.TensorProduct.lid 𝓢 A
      (Algebra.TensorProduct.map (Bialgebra.counitAlgHom 𝓢 A) (AlgHom.id 𝓢 A)
        (algebraIntersectionTensorMap p d A L z)) := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp [hx, hy]
  | tmul a b =>
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      Algebra.TensorProduct.lid_tmul, algebraIntersectionTensorMap_tmul]
    rw [Subalgebra.coe_smul, ← IsScalarTower.algebraMap_smul 𝓢]
    exact congrArg (fun s : 𝓢 ↦ s • (b : A)) (hopfIntersectionCounit_map p d A B e a)

omit P in
/-- The right integral counit agrees with its generic counterpart. -/
theorem hopfIntersectionCounit_rightTensor (z : H ⊗[𝓡] H) :
    ((Algebra.TensorProduct.rid 𝓡 𝓡 H)
      (Algebra.TensorProduct.map (AlgHom.id 𝓡 H) ε z) : A) =
    Algebra.TensorProduct.rid 𝓢 𝓢 A
      (Algebra.TensorProduct.map (AlgHom.id 𝓢 A) (Bialgebra.counitAlgHom 𝓢 A)
        (algebraIntersectionTensorMap p d A L z)) := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp [hx, hy]
  | tmul a b =>
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      Algebra.TensorProduct.rid_tmul, algebraIntersectionTensorMap_tmul]
    rw [Subalgebra.coe_smul, ← IsScalarTower.algebraMap_smul 𝓢]
    exact congrArg (fun s : 𝓢 ↦ s • (a : A)) (hopfIntersectionCounit_map p d A B e b)

/-- The descended comultiplication satisfies the left counit identity. -/
theorem hopfIntersectionComul_leftCounit :
    (Algebra.TensorProduct.map ε (.id 𝓡 H)).comp (hopfIntersectionComul p d A B e P) =
      (Algebra.TensorProduct.lid 𝓡 H).symm := by
  ext a
  apply (Algebra.TensorProduct.lid 𝓡 H).injective
  apply Subtype.ext
  simp only [AlgHom.comp_apply, hopfIntersectionCounit_leftTensor, hopfIntersectionComul_map,
    AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply]
  change TensorProduct.lid 𝓢 A
    (Coalgebra.counit.rTensor A (Coalgebra.comul (R := 𝓢) (a : A))) = (a : A)
  rw [Coalgebra.rTensor_counit_comul, TensorProduct.lid_tmul, one_smul]

/-- The descended comultiplication satisfies the right counit identity. -/
theorem hopfIntersectionComul_rightCounit :
    (Algebra.TensorProduct.map (.id 𝓡 H) ε).comp (hopfIntersectionComul p d A B e P) =
      (Algebra.TensorProduct.rid 𝓡 𝓡 H).symm := by
  ext a
  apply (Algebra.TensorProduct.rid 𝓡 𝓡 H).injective
  apply Subtype.ext
  simp only [AlgHom.comp_apply, hopfIntersectionCounit_rightTensor, hopfIntersectionComul_map,
    AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply]
  change TensorProduct.rid 𝓢 A
    (Coalgebra.counit.lTensor A (Coalgebra.comul (R := 𝓢) (a : A))) = (a : A)
  rw [Coalgebra.lTensor_counit_comul, TensorProduct.rid_tmul, one_smul]

/-- The bialgebra structure on the arithmetic intersection. -/
@[instance_reducible] def hopfIntersectionBialgebra : Bialgebra 𝓡 H :=
  Bialgebra.ofAlgHom (hopfIntersectionComul p d A B e P) ε
    (hopfIntersectionComul_coassoc p d A B e P) (hopfIntersectionComul_leftCounit p d A B e P)
    (hopfIntersectionComul_rightCounit p d A B e P)

omit P in
/-- Left integral convolution agrees with generic convolution. -/
theorem hopfIntersectionAntipode_leftTensor (z : H ⊗[𝓡] H) :
    ((Algebra.TensorProduct.lift (hopfIntersectionAntipode p d A B e) (.id 𝓡 H)
      (fun _ _ ↦ Commute.all _ _)) z : A) =
    LinearMap.mul' 𝓢 A
      ((HopfAlgebra.antipode 𝓢).rTensor A (algebraIntersectionTensorMap p d A L z)) := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp [hx, hy]
  | tmul a b => simp [Algebra.TensorProduct.lift_tmul, hopfIntersectionAntipode]

omit P in
/-- Right integral convolution agrees with generic convolution. -/
theorem hopfIntersectionAntipode_rightTensor (z : H ⊗[𝓡] H) :
    ((Algebra.TensorProduct.lift (.id 𝓡 H) (hopfIntersectionAntipode p d A B e)
      (fun _ _ ↦ Commute.all _ _)) z : A) =
    LinearMap.mul' 𝓢 A
      ((HopfAlgebra.antipode 𝓢).lTensor A (algebraIntersectionTensorMap p d A L z)) := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp [hx, hy]
  | tmul a b => simp [Algebra.TensorProduct.lift_tmul, hopfIntersectionAntipode]

/-- The Hopf algebra structure on the arithmetic intersection. -/
@[instance_reducible] def hopfIntersectionHopfAlgebra : HopfAlgebra 𝓡 H := by
  letI := hopfIntersectionBialgebra p d A B e P
  refine HopfAlgebra.ofAlgHom (hopfIntersectionAntipode p d A B e) ?_ ?_
  · ext a
    change ((Algebra.TensorProduct.lift (hopfIntersectionAntipode p d A B e) (.id 𝓡 H)
      (fun _ _ ↦ Commute.all _ _)) (hopfIntersectionComul p d A B e P a) : A) = algebraMap 𝓡 A (ε a)
    rw [hopfIntersectionAntipode_leftTensor, hopfIntersectionComul_map, Bialgebra.comulAlgHom_apply,
      HopfAlgebra.mul_antipode_rTensor_comul_apply (R := 𝓢) (a : A),
      IsScalarTower.algebraMap_apply 𝓡 𝓢 A]
    exact congrArg (algebraMap 𝓢 A) (hopfIntersectionCounit_map p d A B e a).symm
  · ext a
    change ((Algebra.TensorProduct.lift (.id 𝓡 H) (hopfIntersectionAntipode p d A B e)
      (fun _ _ ↦ Commute.all _ _)) (hopfIntersectionComul p d A B e P a) : A) = algebraMap 𝓡 A (ε a)
    rw [hopfIntersectionAntipode_rightTensor, hopfIntersectionComul_map,
      Bialgebra.comulAlgHom_apply,
      HopfAlgebra.mul_antipode_lTensor_comul_apply (R := 𝓢) (a : A),
      IsScalarTower.algebraMap_apply 𝓡 𝓢 A]
    exact congrArg (algebraMap 𝓢 A) (hopfIntersectionCounit_map p d A B e a).symm


/-- Cocommutativity of the away model descends to the arithmetic intersection. -/
theorem hopfIntersectionCocomm [Coalgebra.IsCocomm 𝓢 A] :
    letI := hopfIntersectionHopfAlgebra p d A B e P
    Coalgebra.IsCocomm 𝓡 H := by
  let := hopfIntersectionHopfAlgebra p d A B e P
  have hc (z : H ⊗[𝓡] H) :
      algebraIntersectionTensorMap p d A L (TensorProduct.comm 𝓡 H H z) =
        TensorProduct.comm 𝓢 A A (algebraIntersectionTensorMap p d A L z) := by
    induction z using TensorProduct.inductionOn with
    | tmul a b => simp
    | add x y hx hy => simp [hx, hy]
  constructor
  apply LinearMap.ext
  intro a
  apply algebraIntersectionTensorMap_injective p d A L P
  change algebraIntersectionTensorMap p d A L
      (TensorProduct.comm 𝓡 H H (hopfIntersectionComul p d A B e P a)) =
    algebraIntersectionTensorMap p d A L (hopfIntersectionComul p d A B e P a)
  rw [hc, hopfIntersectionComul_map]
  exact Coalgebra.comm_comul (R := 𝓢) (a : A)

/-- The descended Hopf algebra is finite flat over the global coefficient ring. -/
theorem hopfIntersectionFiniteFlat :
    letI := hopfIntersectionHopfAlgebra p d A B e P
    HopfAlgebra.IsFiniteFlat 𝓡 H := by
  let := hopfIntersectionHopfAlgebra p d A B e P
  let : Module.Finite 𝓡 H := algebraIntersection_finite p d A L P
  let : Module.Projective 𝓡 H := algebraIntersection_projective p d A L P
  exact ⟨⟩

/-- The away comparison preserves the full bialgebra structure after Hopf descent. -/
def hopfIntersectionAwayBialgEquiv :
    letI := hopfIntersectionHopfAlgebra p d A B e P
    𝓢 ⊗[𝓡] H ≃ₐc[𝓢] A := by
  letI := hopfIntersectionHopfAlgebra p d A B e P
  refine bialgebraScalarExtensionEquiv 𝓡 𝓢 H A (hopfIntersection p d A B e).val
    (by exact algebraIntersectionAwayEquiv p d A L P) ?_ ?_ ?_
  · intro a
    exact (algebraIntersectionAwayMap_tmul p d A L 1 a).trans (one_smul 𝓢 (a : A))
  · intro a
    exact hopfIntersectionCounit_map p d A B e a
  · intro a
    exact hopfIntersectionComul_map p d A B e P a

end ThreeAdicPlan.PadicPatching
