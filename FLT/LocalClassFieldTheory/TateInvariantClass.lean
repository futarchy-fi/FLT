/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.TateNormVanishing

/-!
# Invariants and degree-zero Tate classes

The invariant class map is surjective and its kernel is precisely the image
of the actual group norm. Both statements use the norm differential at the splice.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open CategoryTheory groupCohomology groupHomology

variable {k G : Type} [CommRing k] [Group G] [Fintype G] (M : Rep k G)

/-- An invariant coefficient is a degree-zero Tate cocycle. -/
theorem invariant_tate_cycle (x : M.ρ.invariants) :
    (tateComplex M).d 0 (0 + 1) ((cochainsIso₀ M).inv x) = 0 := by
  change (tateComplex M).d 0 1 ((cochainsIso₀ M).inv x) = 0
  apply (ModuleCat.mono_iff_injective (cochainsIso₁ M).hom).mp inferInstance
  have hd := congrArg (fun f => f.hom ((cochainsIso₀ M).inv (x : M))) (comp_d₀₁_eq M)
  change d₀₁ M ((cochainsIso₀ M).hom ((cochainsIso₀ M).inv x)) =
    (cochainsIso₁ M).hom ((tateComplex M).d 0 1 ((cochainsIso₀ M).inv x)) at hd
  rw [Iso.inv_hom_id_apply] at hd
  rw [← hd, map_zero]
  ext g
  exact sub_eq_zero.mpr (x.property g)

/-- Constant zero-cochains associated to invariant coefficients. -/
def tateInvariantCochain : ModuleCat.of k M.ρ.invariants ⟶ (tateComplex M).X 0 :=
  ModuleCat.ofHom M.ρ.invariants.subtype ≫ (cochainsIso₀ M).inv

/-- The invariant zero-cochain morphism is killed by the Tate differential. -/
theorem tateInvariantCochain_d :
    tateInvariantCochain M ≫ (tateComplex M).d 0 1 = 0 := by
  ext x
  exact invariant_tate_cycle M x

/-- The invariant class map into the actual degree-zero Tate group. -/
def tateInvariantClass : ModuleCat.of k M.ρ.invariants ⟶ tateCohomology M 0 :=
  (tateComplex M).liftCycles (tateInvariantCochain M) 1 (by simp)
    (tateInvariantCochain_d M) ≫ (tateComplex M).homologyπ 0

/-- The invariant class is represented by the corresponding constant zero-cochain. -/
theorem tateInvariantClass_apply (x : M.ρ.invariants) :
    tateInvariantClass M x = tateCocycleClass M 0 ((cochainsIso₀ M).inv x)
      (invariant_tate_cycle M x) := by
  apply congrArg ((tateComplex M).homologyπ 0)
  apply (ModuleCat.mono_iff_injective ((tateComplex M).iCycles 0)).mp inferInstance
  exact (congrArg (fun f : ModuleCat.of k M.ρ.invariants ⟶ (tateComplex M).X 0 => f.hom x)
    ((tateComplex M).liftCycles_i (tateInvariantCochain M) 1 (by simp)
      (tateInvariantCochain_d M))).trans
      ((tateComplex M).i_cyclesMk (i := (0 : ℤ)) ((cochainsIso₀ M).inv (x : M))
        (0 + 1) (by simp) (by exact invariant_tate_cycle M x)).symm

/-- An invariant has zero Tate class exactly when it is a norm. -/
theorem tateInvariantClass_eq_zero_iff (x : M.ρ.invariants) :
    tateInvariantClass M x = 0 ↔ ∃ y : M, M.norm.hom y = (x : M) := by
  rw [tateInvariantClass_apply, tateCocycleClass_eq_zero_iff]
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨(chainsIso₀ M).hom b, ?_⟩
    have he := congrArg (cochainsIso₀ M).hom hb
    change (cochainsIso₀ M).hom ((cochainsIso₀ M).inv
      (M.norm.hom ((chainsIso₀ M).hom b))) = (cochainsIso₀ M).hom ((cochainsIso₀ M).inv x) at he
    simpa only [Iso.inv_hom_id_apply] using he
  · rintro ⟨y, hy⟩
    refine ⟨(chainsIso₀ M).inv y, ?_⟩
    change (cochainsIso₀ M).inv (M.norm.hom
      ((chainsIso₀ M).hom ((chainsIso₀ M).inv y))) = (cochainsIso₀ M).inv x
    rw [Iso.inv_hom_id_apply, hy]

/-- Every degree-zero Tate class is the class of an invariant coefficient. -/
theorem tateInvariantClass_surjective : Function.Surjective (tateInvariantClass M) := by
  intro a
  obtain ⟨z, hz, rfl⟩ := tateCocycleClass_surjective M 0 a
  change (tateComplex M).d 0 1 z = 0 at hz
  have hf : d₀₁ M ((cochainsIso₀ M).hom z) = 0 := by
    have hd := congrArg (fun f => f.hom z) (comp_d₀₁_eq M)
    change d₀₁ M ((cochainsIso₀ M).hom z) =
      (cochainsIso₁ M).hom ((tateComplex M).d 0 1 z) at hd
    simpa only [hz, map_zero] using hd
  let x : M.ρ.invariants := ⟨(cochainsIso₀ M).hom z,
    fun g => sub_eq_zero.mp (congrFun hf g)⟩
  refine ⟨x, ?_⟩
  rw [tateInvariantClass_apply]
  congr 1
  exact (cochainsIso₀ M).hom_inv_id_apply z

end LocalClassFieldTheory
