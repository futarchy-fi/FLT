/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.FiniteFlat
public import FLT.GroupScheme.PadicAlgebraPatching

/-!
# Hopf operations on the arithmetic intersection

A bialgebra comparison of the local generic fibres makes the local algebra a
lattice in the away generic fibre. The intersection preserves Hopf operations.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local instance 100000] CommRing.toCommSemiring CommSemiring.toSemiring
  Algebra.toSMul Algebra.toModule
  Subalgebra.toCommRing Subalgebra.toRing Ring.toAddCommGroup AddCommGroup.toAddGroup

open scoped TensorProduct

namespace ThreeAdicPlan.PadicPatching

variable (p : ℕ) [Fact p.Prime] (d : ℤ) [Fact (¬ (p : ℤ) ∣ d)]
    (A B : Type) [CommRing A] [CommRing B]
    [HopfAlgebra (Away d p) A] [HopfAlgebra ℤ_[p] B]
    [Algebra (Base d) A] [IsScalarTower (Base d) (Away d p) A]
    (e : ℚ_[p] ⊗[ℤ_[p]] B ≃ₐc[ℚ_[p]] ℚ_[p] ⊗[Away d p] A)

/-- Use the module inherited from the away Hopf algebra. -/
local instance : Module (Away d p) A := by
  exact Algebra.toModule

/-- The local algebra embedded into the common generic fibre using the given
bialgebra comparison. -/
def localHopfMap : B →ₐ[ℤ_[p]] ℚ_[p] ⊗[Away d p] A :=
  (e.toAlgEquiv.toAlgHom.restrictScalars ℤ_[p]).comp Algebra.TensorProduct.includeRight

/-- The local algebra as a subalgebra of the common generic fibre. -/
def localHopfLattice : Subalgebra ℤ_[p] (ℚ_[p] ⊗[Away d p] A) :=
  (localHopfMap p d A B e).range

/-- The algebra intersection associated to compatible away and local Hopf algebras. -/
abbrev hopfIntersection := algebraIntersection p d A (localHopfLattice p d A B e)

omit [Algebra (Base d) A] [IsScalarTower (Base d) (Away d p) A] in
@[simp] theorem localHopfMap_apply (b : B) :
    localHopfMap p d A B e b = e (1 ⊗ₜ[ℤ_[p]] b) := rfl

omit [Algebra (Base d) A] [IsScalarTower (Base d) (Away d p) A] in
/-- Counits of compatible generic fibres agree in the local field. -/
theorem localHopfMap_counit (b : B) :
    Coalgebra.counit (R := ℚ_[p]) (localHopfMap p d A B e b) =
      algebraMap ℤ_[p] ℚ_[p] (Coalgebra.counit (R := ℤ_[p]) b) := by
  rw [localHopfMap_apply, CoalgHomClass.counit_comp_apply]
  simp [Algebra.smul_def]

omit [Algebra (Base d) A] [IsScalarTower (Base d) (Away d p) A] in
/-- Antipodes of compatible generic fibres agree on the local algebra. -/
theorem localHopfMap_antipode (b : B) :
    HopfAlgebra.antipode ℚ_[p] (localHopfMap p d A B e b) =
      localHopfMap p d A B e (HopfAlgebra.antipode ℤ_[p] b) := by
  have h := LinearMap.congr_fun (BialgHom.antipode_comp e.toBialgHom) (1 ⊗ₜ[ℤ_[p]] b)
  change HopfAlgebra.antipode ℚ_[p] (e (1 ⊗ₜ[ℤ_[p]] b)) =
    e (HopfAlgebra.antipode ℚ_[p] (1 ⊗ₜ[ℤ_[p]] b)) at h
  simpa only [TensorProduct.antipode_def, TensorProduct.AlgebraTensorModule.map_tmul,
    HopfAlgebra.antipode_one, localHopfMap_apply] using h

/-- The away antipode restricts to the intersection algebra. -/
theorem antipode_mem_hopfIntersection (a : hopfIntersection p d A B e) :
    (HopfAlgebra.antipodeAlgHom (Away d p) A) (a : A) ∈ hopfIntersection p d A B e := by
  obtain ⟨b, hb⟩ := a.property
  change localHopfMap p d A B e b = (1 : ℚ_[p]) ⊗ₜ[Away d p] (a : A) at hb
  refine ⟨HopfAlgebra.antipode ℤ_[p] b, ?_⟩
  change localHopfMap p d A B e (HopfAlgebra.antipode ℤ_[p] b) = _
  rw [← localHopfMap_antipode, hb]
  simp [TensorProduct.antipode_def]

/-- The integral antipode is the restriction of the away antipode. -/
def hopfIntersectionAntipode : hopfIntersection p d A B e →ₐ[Base d]
    hopfIntersection p d A B e :=
  (((HopfAlgebra.antipodeAlgHom (Away d p) A).restrictScalars (Base d)).comp
    (hopfIntersection p d A B e).val).codRestrict
      (hopfIntersection p d A B e) (antipode_mem_hopfIntersection p d A B e)

/-- The away counit of an intersection element comes from the global base ring. -/
theorem counit_mem_base (a : hopfIntersection p d A B e) :
    ∃ r : Base d, (Algebra.ofId (Base d) (Away d p)) r =
      (Bialgebra.counitAlgHom (Away d p) A) (a : A) := by
  obtain ⟨b, hb⟩ := a.property
  change localHopfMap p d A B e b = (1 : ℚ_[p]) ⊗ₜ[Away d p] (a : A) at hb
  have hc := congrArg (Coalgebra.counit (R := ℚ_[p])) hb
  rw [localHopfMap_counit] at hc
  simp only [TensorProduct.counit_tmul, CommSemiring.counit_apply,
    Algebra.smul_def, mul_one] at hc
  obtain ⟨r, hr⟩ := exists_away_of_padic_integral p d (Base d) (Away d p)
    ((Bialgebra.counitAlgHom (Away d p) A) (a : A)) (by
      change ‖algebraMap (Away d p) ℚ_[p] (Coalgebra.counit (R := Away d p) (a : A))‖ ≤ 1
      rw [← hc]
      exact PadicInt.norm_le_one _)
  refine ⟨r, ?_⟩
  apply FaithfulSMul.algebraMap_injective (Away d p) ℚ_[p]
  change algebraMap (Away d p) ℚ_[p] (algebraMap (Base d) (Away d p) r) = _
  rw [← IsScalarTower.algebraMap_apply (Base d) (Away d p) ℚ_[p]]
  exact hr


/-- The descended counit, obtained by restricting the away counit to the global
base ring. -/
def hopfIntersectionCounit : hopfIntersection p d A B e →ₐ[Base d] Base d := by
  let : NeZero d := ⟨denominator_ne_zero p d⟩
  let i : Base d →ₐ[Base d] Away d p := Algebra.ofId _ _
  have hi : Function.Injective i := by
    apply IsLocalization.injective (M := Submonoid.powers (p : Base d)) (Away d p)
    rintro x ⟨n, rfl⟩
    apply pow_mem
    apply mem_nonZeroDivisors_of_ne_zero
    intro hp
    have hq : (p : ℚ_[p]) = 0 := by simpa using congrArg (algebraMap (Base d) ℚ_[p]) hp
    exact (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) hq
  let f : hopfIntersection p d A B e →ₐ[Base d] i.range :=
    (((Bialgebra.counitAlgHom (Away d p) A).restrictScalars (Base d)).comp
      (hopfIntersection p d A B e).val).codRestrict i.range (fun a ↦ counit_mem_base p d A B e a)
  exact (AlgEquiv.ofInjective i hi).symm.toAlgHom.comp f

/-- The descended counit agrees with the away counit. -/
theorem hopfIntersectionCounit_map (a : hopfIntersection p d A B e) :
    (Algebra.ofId (Base d) (Away d p)) (hopfIntersectionCounit p d A B e a) =
      (Bialgebra.counitAlgHom (Away d p) A) (a : A) := by
  let : NeZero d := ⟨denominator_ne_zero p d⟩
  let i : Base d →ₐ[Base d] Away d p := Algebra.ofId _ _
  have hi : Function.Injective i := by
    apply IsLocalization.injective (M := Submonoid.powers (p : Base d)) (Away d p)
    rintro x ⟨n, rfl⟩
    apply pow_mem
    apply mem_nonZeroDivisors_of_ne_zero
    intro hp
    have hq : (p : ℚ_[p]) = 0 := by simpa using congrArg (algebraMap (Base d) ℚ_[p]) hp
    exact (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) hq
  let ei := AlgEquiv.ofInjective i hi
  exact congrArg Subtype.val (ei.apply_symm_apply
    ⟨(Bialgebra.counitAlgHom (Away d p) A) (a : A), counit_mem_base p d A B e a⟩)

/-- The local algebra maps linearly onto the lattice used in module patching. -/
def localHopfLatticeMap : B →ₗ[ℤ_[p]] (localHopfLattice p d A B e).toSubmodule :=
  (localHopfLattice p d A B e).toSubmoduleEquiv.symm.toLinearMap.comp
    (localHopfMap p d A B e).rangeRestrict.toLinearMap

omit [Algebra (Base d) A] [IsScalarTower (Base d) (Away d p) A] in
/-- Tensoring the local lattice map agrees with the generic bialgebra comparison. -/
theorem localHopfLatticeMap_tensor (z : B ⊗[ℤ_[p]] B) :
    latticeTensorMap (p := p) (d := d) (M := A)
      (TensorProduct.map (localHopfLatticeMap p d A B e) (localHopfLatticeMap p d A B e) z) =
    TensorProduct.map e.toLinearMap e.toLinearMap
      ((HopfAlgebra.IntegralClosure.baseChangeTensorEquiv ℤ_[p] ℚ_[p] B B).symm
        (1 ⊗ₜ[ℤ_[p]] z)) := by
  induction z using TensorProduct.inductionOn with
  | tmul b c =>
    simp [localHopfLatticeMap, localHopfLattice, localHopfMap, Subalgebra.toSubmoduleEquiv,
      HopfAlgebra.IntegralClosure.baseChangeTensorEquiv]
    rfl
  | add a b ha hb => simpa [TensorProduct.tmul_add] using congrArg₂ (· + ·) ha hb

omit [Algebra (Base d) A] [IsScalarTower (Base d) (Away d p) A] in
/-- The local comultiplication lands in the tensor square of the local lattice. -/
theorem localHopfLatticeMap_comul (b : B) :
    latticeTensorMap (p := p) (d := d) (M := A) (TensorProduct.map (localHopfLatticeMap p d A B e)
      (localHopfLatticeMap p d A B e) (Coalgebra.comul (R := ℤ_[p]) b)) =
    Coalgebra.comul (R := ℚ_[p]) (localHopfMap p d A B e b) := by
  rw [localHopfLatticeMap_tensor]
  have h := HopfAlgebra.IntegralClosure.baseChange_comul_includeRight ℤ_[p] ℚ_[p] B b
  simp only [Algebra.TensorProduct.includeRight_apply] at h
  rw [← h, AlgEquiv.symm_apply_apply]
  exact CoalgHomClass.map_comp_comul_apply e (1 ⊗ₜ[ℤ_[p]] b)

omit [Algebra (Base d) A] [IsScalarTower (Base d) (Away d p) A] in
/-- Base change carries away comultiplication to generic comultiplication. -/
theorem awayTensorMap_comul (a : A) :
    awayTensorMap (p := p) (d := d) (M := A) (Coalgebra.comul (R := Away d p) a) =
      Coalgebra.comul (R := ℚ_[p]) ((1 : ℚ_[p]) ⊗ₜ[Away d p] a) := by
  have h := HopfAlgebra.IntegralClosure.baseChange_comul_includeRight (Away d p) ℚ_[p] A a
  simp only [Algebra.TensorProduct.includeRight_apply] at h
  have he (z : A ⊗[Away d p] A) : awayTensorMap (p := p) (d := d) (M := A) z =
      (HopfAlgebra.IntegralClosure.baseChangeTensorEquiv (Away d p) ℚ_[p] A A).symm
        (1 ⊗ₜ[Away d p] z) := by
    induction z using TensorProduct.inductionOn with
    | tmul x y => simp [HopfAlgebra.IntegralClosure.baseChangeTensorEquiv]
    | add a b ha hb => simpa [TensorProduct.tmul_add] using congrArg₂ (· + ·) ha hb
  rw [he, ← h, AlgEquiv.symm_apply_apply]

variable (P : ModulePatch p d A (localHopfLattice p d A B e).toSubmodule)

include P in
/-- The away comultiplication of an intersection element belongs to the actual
integral tensor square. -/
theorem comul_mem_intersectionTensor (a : hopfIntersection p d A B e) :
    ∃ z, algebraIntersectionTensorMap p d A (localHopfLattice p d A B e) z =
      (Bialgebra.comulAlgHom (Away d p) A) (a : A) := by
  apply (algebraIntersectionTensorMap_range p d A (localHopfLattice p d A B e) P _).2
  obtain ⟨b, hb⟩ := a.property
  change localHopfMap p d A B e b = (1 : ℚ_[p]) ⊗ₜ[Away d p] (a : A) at hb
  refine ⟨TensorProduct.map (localHopfLatticeMap p d A B e)
    (localHopfLatticeMap p d A B e) (Coalgebra.comul (R := ℤ_[p]) b), ?_⟩
  rw [localHopfLatticeMap_comul, hb]
  exact awayTensorMap_comul p d A (a : A)

/-- Comultiplication on the intersection, using tensor-compatible patching to
restrict the away comultiplication. -/
def hopfIntersectionComul : hopfIntersection p d A B e →ₐ[Base d]
    hopfIntersection p d A B e ⊗[Base d] hopfIntersection p d A B e := by
  let i := algebraIntersectionTensorMap p d A (localHopfLattice p d A B e)
  let f : hopfIntersection p d A B e →ₐ[Base d] i.range :=
    (((Bialgebra.comulAlgHom (Away d p) A).restrictScalars (Base d)).comp
      (hopfIntersection p d A B e).val).codRestrict i.range
        (comul_mem_intersectionTensor p d A B e P)
  exact (AlgEquiv.ofInjective i
    (algebraIntersectionTensorMap_injective p d A
      (localHopfLattice p d A B e) P)).symm.toAlgHom.comp f

/-- The descended comultiplication agrees with the away comultiplication. -/
theorem hopfIntersectionComul_map (a : hopfIntersection p d A B e) :
    algebraIntersectionTensorMap p d A (localHopfLattice p d A B e)
      (hopfIntersectionComul p d A B e P a) =
        (Bialgebra.comulAlgHom (Away d p) A) (a : A) := by
  let i := algebraIntersectionTensorMap p d A (localHopfLattice p d A B e)
  let ei := AlgEquiv.ofInjective i
    (algebraIntersectionTensorMap_injective p d A (localHopfLattice p d A B e) P)
  exact congrArg Subtype.val (ei.apply_symm_apply
    ⟨(Bialgebra.comulAlgHom (Away d p) A) (a : A),
      comul_mem_intersectionTensor p d A B e P a⟩)


omit [Algebra (Base d) A] [IsScalarTower (Base d) (Away d p) A] in
/-- A finite local algebra gives a finitely generated lattice in the common fibre. -/
theorem localHopfLattice_fg [Module.Finite ℤ_[p] B] :
    (localHopfLattice p d A B e).toSubmodule.FG := by
  change (localHopfMap p d A B e).toLinearMap.range.FG
  exact Submodule.fg_range _

omit [Algebra (Base d) A] [IsScalarTower (Base d) (Away d p) A] in
/-- The local algebra lattice spans the common generic fibre. -/
theorem localHopfLattice_span :
    Submodule.span ℚ_[p] (localHopfLattice p d A B e : Set (ℚ_[p] ⊗[Away d p] A)) = ⊤ := by
  apply top_le_iff.mp
  intro z hz
  clear hz
  obtain ⟨x, hx⟩ := e.surjective z
  change e x = z at hx
  rw [← hx]
  clear hx
  induction x using TensorProduct.inductionOn with
  | tmul r b =>
    have hb : localHopfMap p d A B e b ∈
        Submodule.span ℚ_[p] (localHopfLattice p d A B e : Set (ℚ_[p] ⊗[Away d p] A)) :=
      Submodule.subset_span ((localHopfMap p d A B e).mem_range_self b)
    have hr : e (r ⊗ₜ[ℤ_[p]] b) = r • localHopfMap p d A B e b := by
      rw [localHopfMap_apply, ← map_smul]
      congr 1
      simp [TensorProduct.smul_tmul']
    rw [hr]
    exact Submodule.smul_mem _ r hb
  | add x y hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy

/-- The module patch needed by Hopf descent exists for every finite projective
away algebra and finite local algebra with identified generic fibres. -/
def hopfModulePatch [Module.Finite (Away d p) A] [Module.Projective (Away d p) A]
    [Module.Finite ℤ_[p] B] : ModulePatch p d A (localHopfLattice p d A B e).toSubmodule :=
  patchModule p d A (localHopfLattice p d A B e).toSubmodule
    (localHopfLattice_fg p d A B e) (localHopfLattice_span p d A B e)

end ThreeAdicPlan.PadicPatching
