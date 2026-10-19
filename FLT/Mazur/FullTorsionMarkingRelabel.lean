/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.Algebra.Group.End

/-!
# Relabeling full torsion markings

An isomorphism between groups with faithful full torsion markings induces a
unique automorphism of the label group. No choice of a basis or etaleness is used.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.FullTorsionMarking
universe u v w
variable {L : Type u} {A : Type v} {B : Type w} [Group L] [Group A] [Group B]
  (n : ℕ) (m : L →* A) (v : L →* B)
  (hm : Function.Injective m) (hv : Function.Injective v)
  (hmp : ∀ a, m a ^ n = 1) (hvp : ∀ a, v a ^ n = 1)
  (hmf : ∀ x : A, x ^ n = 1 → ∃ a, m a = x)
  (hvf : ∀ x : B, x ^ n = 1 → ∃ a, v a = x) (e : A ≃* B)

include hm hv hmp hvp hmf hvf in
/-- Full faithful torsion labels are matched by a unique label automorphism. -/
theorem existsUnique_relabel : ∃! r : MulAut L, ∀ a, e (m (r a)) = v a := by
  have hex (a : L) : ∃ b, m b = e.symm (v a) := by
    apply hmf
    rw [← map_pow, hvp, map_one]
  let k : L → L := fun a ↦ Classical.choose (hex a)
  have hk (a : L) : m (k a) = e.symm (v a) := Classical.choose_spec (hex a)
  have hki : Function.Injective k := by
    intro a b h
    apply hv
    apply e.symm.injective
    rw [← hk, ← hk, h]
  have hks : Function.Surjective k := by
    intro a
    obtain ⟨b, hb⟩ := hvf (e (m a)) (by rw [← map_pow, hmp, map_one])
    refine ⟨b, hm ?_⟩
    rw [hk, hb, e.symm_apply_apply]
  let kh : L →* L :=
    { toFun := k
      map_one' := by apply hm; rw [hk, map_one, map_one, map_one]
      map_mul' := by
        intro a b
        apply hm
        rw [hk, map_mul, map_mul, map_mul, hk, hk] }
  let r : MulAut L := MulEquiv.ofBijective kh ⟨hki, hks⟩
  have hr (a : L) : e (m (r a)) = v a := by
    change e (m (k a)) = v a
    rw [hk, e.apply_symm_apply]
  refine ⟨r, hr, ?_⟩
  intro s hs
  apply MulEquiv.ext
  intro a
  apply hm
  apply e.injective
  exact (hs a).trans (hr a).symm

end FLT.Mazur.FullTorsionMarking
