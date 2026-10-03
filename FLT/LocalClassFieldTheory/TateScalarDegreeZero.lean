/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.TateClassArithmetic
public import FLT.LocalClassFieldTheory.TateCupUnit

/-!
# Scalar Tate cohomology in degree zero

Every integral scalar class is a multiple of the unit, and the group order
kills that unit by the actual norm differential of the Tate complex.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open CategoryTheory groupCohomology groupHomology

variable (G : Type) [Group G] [Fintype G]

local notation "T" => Rep.trivial ℤ G ℤ

/-- Every degree-zero scalar Tate class is an integer multiple of the actual unit class. -/
theorem tateScalarUnit_generates (a : tateCohomology T 0) :
    ∃ m : ℤ, m • tateScalarUnit ℤ G = a := by
  obtain ⟨z, hz, rfl⟩ := tateCocycleClass_surjective T 0 a
  let m : ℤ := z (fun i => Fin.elim0 i)
  have he : z = m • (fun _ : Fin 0 → G => (1 : ℤ)) := by
    funext v
    change z v = m * 1
    rw [mul_one]
    change z v = z (fun i => Fin.elim0 i)
    congr 1
    funext i
    exact Fin.elim0 i
  have h1 : (tateComplex T).d 0 1 (fun _ => (1 : ℤ)) = 0 := by
    exact scalarOne_cycle ℤ G
  have hm : (tateComplex T).d 0 1 (m • (fun _ => (1 : ℤ))) = 0 := by
    rw [map_zsmul, h1, smul_zero]
  refine ⟨m, (tateCocycleClass_zsmul T 0 m _ h1 hm).symm.trans ?_⟩
  congr 1
  exact he.symm

/-- The norm of the degree-minus-one scalar lift of `1` is the constant group order. -/
theorem tateScalar_norm_one :
    (tateComplex T).d (-1) 0 ((chainsIso₀ T).inv (1 : ℤ)) =
      (Fintype.card G : ℤ) • (fun _ : Fin 0 → G => (1 : ℤ)) := by
  rw [tateComplex_d_neg_one]
  have hc := (chainsIso₀ T).inv_hom_id_apply (1 : ℤ)
  change (cochainsIso₀ T).inv ((Rep.norm T).hom
    ((chainsIso₀ T).hom ((chainsIso₀ T).inv (1 : ℤ)))) = _
  rw [hc]
  funext v
  change (Rep.norm T).hom (1 : ℤ) = (Fintype.card G : ℤ) * 1
  simp [Rep.norm, Representation.norm]

/-- The group order annihilates the actual scalar Tate unit. -/
theorem tateScalarUnit_card_smul : (Fintype.card G : ℤ) • tateScalarUnit ℤ G = 0 := by
  have h1 : (tateComplex T).d 0 1 (fun _ => (1 : ℤ)) = 0 := by
    exact scalarOne_cycle ℤ G
  have hm : (tateComplex T).d 0 1
      ((Fintype.card G : ℤ) • (fun _ => (1 : ℤ))) = 0 := by
    rw [map_zsmul, h1, smul_zero]
  exact (tateCocycleClass_zsmul T 0 (Fintype.card G : ℤ) _ h1 hm).symm.trans
    ((tateCocycleClass_eq_zero_iff T 0 _ hm).mpr
      ⟨(chainsIso₀ T).inv (1 : ℤ), tateScalar_norm_one G⟩)

end LocalClassFieldTheory
