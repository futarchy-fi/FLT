/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.SubgroupNormDecomposition

/-!
# Summation along a finite surjective group homomorphism

Every fiber has the cardinality of the kernel. The explicit coordinates
keep this multiplicity visible in inflation computations.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

variable {G H : Type} [Group G] [Group H]

/-- Coordinates on a surjective homomorphism using a chosen lift and its kernel. -/
def homFiberEquiv (f : G →* H) (hf : Function.Surjective f) : H × f.ker ≃ G where
  toFun x := (hf x.1).choose * x.2
  invFun g := ⟨f g, ⟨(hf (f g)).choose⁻¹ * g, by
    simp only [MonoidHom.mem_ker, map_mul, map_inv, (hf (f g)).choose_spec, inv_mul_cancel]⟩⟩
  left_inv x := by
    have he : f ((hf x.1).choose * x.2) = x.1 := by
      rw [map_mul, (hf x.1).choose_spec, x.2.property, mul_one]
    apply Prod.ext he
    apply Subtype.ext
    simp only [he, inv_mul_cancel_left]
  right_inv g := mul_inv_cancel_left _ g

/-- Summing a function pulled back through a surjection counts each kernel fiber. -/
theorem sum_surjective_hom [Fintype G] [Fintype H]
    (f : G →* H) (hf : Function.Surjective f)
    {A : Type*} [AddCommMonoid A] (a : H → A) :
    ∑ g : G, a (f g) = Nat.card f.ker • ∑ h : H, a h := by
  classical
  let : Fintype f.ker := Fintype.ofFinite _
  rw [← (homFiberEquiv f hf).sum_comp, Fintype.sum_prod_type]
  have he (h : H) (n : f.ker) : f (homFiberEquiv f hf (h, n)) = h := by
    change f ((hf h).choose * n) = h
    rw [map_mul, (hf h).choose_spec, n.property, mul_one]
  simp only [he, Finset.sum_const, Finset.card_univ, ← Finset.smul_sum,
    Nat.card_eq_fintype_card]

end LocalClassFieldTheory
