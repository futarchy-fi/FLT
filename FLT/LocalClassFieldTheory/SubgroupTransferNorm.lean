/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.SubgroupNormDecomposition
public import FLT.LocalClassFieldTheory.TransferCochain

/-!
# Coset transfer at the Tate norm splice

The zero-cochain transfer is the sum of representative actions. It commutes
with the zero-cochain differential and takes the subgroup norm to the full
norm, so it joins the covariant map on chains at the Tate splice.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open CategoryTheory groupCohomology groupHomology

variable {k G : Type} [CommRing k] [Group G]
  (M : Rep k G) (H : Subgroup G) [Fintype (G ⧸ H)]

/-- Transfer of zero-cochains is the sum of the left representative actions. -/
def transferZero : M →ₗ[k] M := ∑ q : G ⧸ H, M.ρ q.out

/-- The zero-cochain transfer evaluated as a coset sum. -/
theorem transferZero_apply (x : M) :
    transferZero M H x = ∑ q : G ⧸ H, M.ρ q.out x := by
  classical
  exact LinearMap.sum_apply _ _ _

/-- Transfer commutes with the differential from zero-cochains to one-cochains. -/
theorem transferZero_d (x : M) (g : G) :
    (∑ q : G ⧸ H, M.ρ q.out
      ((Rep.res H.subtype M).ρ (transferTransport H g q) x - x)) =
        M.ρ g (transferZero M H x) - transferZero M H x := by
  classical
  simp only [map_sub, Finset.sum_sub_distrib, transferZero_apply]
  congr 1
  calc
    _ = ∑ q : G ⧸ H, M.ρ g (M.ρ (g⁻¹ • q).out x) := by
      apply Finset.sum_congr rfl
      intro q _
      change M.ρ q.out (M.ρ (transferTransport H g q : G) x) = _
      rw [← Module.End.mul_apply, ← map_mul, transferTransport_spec, map_mul]
      rfl
    _ = M.ρ g (∑ q : G ⧸ H, M.ρ q.out x) := by
      rw [map_sum]
      exact Equiv.sum_comp (MulAction.toPerm g⁻¹)
        (fun q : G ⧸ H => M.ρ g (M.ρ q.out x))

/-- Transfer of an invariant coefficient is invariant under the full group. -/
def transferInvariant :
    (Rep.res H.subtype M).ρ.invariants →ₗ[k] M.ρ.invariants :=
  ((transferZero M H).comp (Rep.res H.subtype M).ρ.invariants.subtype).codRestrict _
    fun x g => by
      have h := transferZero_d M H x g
      have hx (a : H) : (Rep.res H.subtype M).ρ a (x : M) = x := x.property a
      simp only [hx, sub_self, map_zero, Finset.sum_const_zero] at h
      exact sub_eq_zero.mp h.symm

/-- Restriction followed by transfer multiplies an invariant by the subgroup index. -/
theorem transferZero_of_invariant (x : M.ρ.invariants) :
    transferZero M H x = Fintype.card (G ⧸ H) • (x : M) := by
  classical
  have hx (g : G) : M.ρ g (x : M) = x := x.property g
  simp [transferZero_apply, hx]

variable [Fintype G] [Fintype H]

/-- Transfer takes the subgroup norm to the full norm. -/
theorem transferZero_norm (x : M) :
    transferZero M H ((Rep.res H.subtype M).norm.hom x) = M.norm.hom x := by
  rw [transferZero_apply, norm_sum_cosets M H x]

/-- The zero-cochain component of corestriction on the Tate complex. -/
def transferZeroCochain :
    (inhomogeneousCochains (Rep.res H.subtype M)).X 0 ⟶
      (inhomogeneousCochains M).X 0 :=
  (cochainsIso₀ (Rep.res H.subtype M)).hom ≫
    ModuleCat.ofHom (transferZero M H) ≫ (cochainsIso₀ M).inv

/-- The actual chain inclusion and zero-cochain transfer commute with the Tate norm. -/
theorem transfer_norm_square :
    (chainsMap H.subtype (𝟙 (Rep.res H.subtype M))).f 0 ≫ M.tateNorm =
      (Rep.res H.subtype M).tateNorm ≫ transferZeroCochain M H := by
  rw [← cancel_mono (cochainsIso₀ M).hom]
  simp only [Rep.tateNorm, transferZeroCochain, Category.assoc,
    Iso.inv_hom_id, Category.comp_id, Iso.inv_hom_id_assoc]
  rw [← Category.assoc, chainsMap_f_0_comp_chainsIso₀]
  ext x
  exact (transferZero_norm M H _).symm

end LocalClassFieldTheory
