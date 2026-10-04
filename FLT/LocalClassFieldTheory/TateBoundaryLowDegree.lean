/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.OneCocycleNegativeBoundary
public import FLT.LocalClassFieldTheory.TateInvariantClass

/-!
# Concrete negative Tate boundaries

The two differentials at the negative splice are the action difference and
norm. These formulas apply to arbitrary short exact coefficient sequences.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open CategoryTheory groupCohomology groupHomology

variable {k G : Type} [CommRing k] [Group G] [Fintype G]

/-- A coefficient map acts coefficientwise on zero-chains. -/
theorem tate_map_negative_one {A B : Rep k G} (f : A ⟶ B) (x : A) :
    (tateComplex.map f).f (-1) ((chainsIso₀ A).inv x) =
      (chainsIso₀ B).inv (f.hom x) := by
  apply (ModuleCat.mono_iff_injective (chainsIso₀ B).hom).mp inferInstance
  have h := congrArg (fun t => t.hom ((chainsIso₀ A).inv x))
    (chainsMap_f_0_comp_chainsIso₀ (MonoidHom.id G) f)
  change (chainsIso₀ B).hom ((tateComplex.map f).f (-1) _) =
    f.hom ((chainsIso₀ A).hom ((chainsIso₀ A).inv x)) at h
  rw [Iso.inv_hom_id_apply] at h ⊢
  exact h

/-- A coefficient map acts coefficientwise on zero-cochains. -/
theorem tate_map_zero {A B : Rep k G} (f : A ⟶ B) (x : A) :
    (tateComplex.map f).f 0 ((cochainsIso₀ A).inv x) =
      (cochainsIso₀ B).inv (f.hom x) := by
  apply (ModuleCat.mono_iff_injective (cochainsIso₀ B).hom).mp inferInstance
  have h := congrArg (fun t => t.hom ((cochainsIso₀ A).inv x))
    (cochainsMap_f_0_comp_cochainsIso₀ (MonoidHom.id G) f)
  change (cochainsIso₀ B).hom ((tateComplex.map f).f 0 _) =
    f.hom ((cochainsIso₀ A).hom ((cochainsIso₀ A).inv x)) at h
  rw [Iso.inv_hom_id_apply] at h ⊢
  exact h

/-- The negative differential of a single chain is the inverse-action difference. -/
theorem tate_single_d (A : Rep k G) (g : G) (x : A) :
    (tateComplex A).d (-2) (-2 + 1) ((chainsIso₁ A).inv (Finsupp.single g x)) =
      (chainsIso₀ A).inv (A.ρ g⁻¹ x - x) := by
  have h := congrArg (fun t => t.hom (Finsupp.single g x)) (eq_d₁₀_comp_inv A)
  change (inhomogeneousChains A).d 1 0 ((chainsIso₁ A).inv _) =
    (chainsIso₀ A).inv (d₁₀ A (Finsupp.single g x)) at h
  change (inhomogeneousChains A).d 1 0 _ = _
  rw [h, d₁₀_single]

/-- The first negative connecting class comes from an action difference of a lift. -/
theorem tate_boundary_negative_two
    (S : ShortComplex (Rep k G)) (hS : S.ShortExact)
    (g : G) (z : S.X₃)
    (hz : (tateComplex S.X₃).d (-2) (-2 + 1)
      ((chainsIso₁ S.X₃).inv (Finsupp.single g z)) = 0)
    (x : S.X₂) (hx : S.g.hom x = z) (y : S.X₁)
    (hy : S.f.hom y = S.X₂.ρ g⁻¹ x - x) :
    ∃ hyz, TateCohomology.δ hS (-2)
      (tateCocycleClass S.X₃ (-2) ((chainsIso₁ S.X₃).inv (Finsupp.single g z)) hz) =
      tateCocycleClass S.X₁ (-1) ((chainsIso₀ S.X₁).inv y) hyz := by
  have hd : (tateComplex.map S.f).f (-1) ((chainsIso₀ S.X₁).inv y) =
      (tateComplex S.X₂).d (-2) (-2 + 1)
        ((chainsIso₁ S.X₂).inv (Finsupp.single g x)) := by
    rw [tate_map_negative_one, tate_single_d, hy]
  refine ⟨tateConnecting_cycle hS (-2) _ _ hd, ?_⟩
  apply tateConnecting_apply hS (-2) _ hz
    ((chainsIso₁ S.X₂).inv (Finsupp.single g x)) _ _ hd
  apply (ModuleCat.mono_iff_injective (chainsIso₁ S.X₃).hom).mp inferInstance
  have h := congrArg (fun t => t.hom
    ((chainsIso₁ S.X₂).inv (Finsupp.single g x)))
    (chainsMap_f_1_comp_chainsIso₁ (MonoidHom.id G) S.g)
  change (chainsIso₁ S.X₃).hom ((tateComplex.map S.g).f (-2) _) =
    chainsMap₁ (MonoidHom.id G) S.g
      ((chainsIso₁ S.X₂).hom ((chainsIso₁ S.X₂).inv _)) at h
  rw [Iso.inv_hom_id_apply] at h ⊢
  exact h.trans (by simp [chainsMap₁, hx])

/-- The second negative boundary is the invariant norm of a lifted zero-chain. -/
theorem tate_boundary_negative_one
    (S : ShortComplex (Rep k G)) (hS : S.ShortExact)
    (z : S.X₃) (hz : (tateComplex S.X₃).d (-1) (-1 + 1)
      ((chainsIso₀ S.X₃).inv z) = 0)
    (y : S.X₂) (hy : S.g.hom y = z)
    (a : S.X₁.ρ.invariants) (ha : S.f.hom a = S.X₂.norm.hom y) :
    TateCohomology.δ hS (-1)
      (tateCocycleClass S.X₃ (-1) ((chainsIso₀ S.X₃).inv z) hz) =
        tateInvariantClass S.X₁ a := by
  rw [tateInvariantClass_apply]
  apply tateConnecting_apply hS (-1) _ hz ((chainsIso₀ S.X₂).inv y)
  · rw [tate_map_negative_one, hy]
  · change (tateComplex.map S.f).f 0 ((cochainsIso₀ S.X₁).inv a) = _
    rw [tate_map_zero, ha]
    change _ = (cochainsIso₀ S.X₂).inv
      (S.X₂.norm.hom ((chainsIso₀ S.X₂).hom ((chainsIso₀ S.X₂).inv y)))
    rw [Iso.inv_hom_id_apply]

end LocalClassFieldTheory
