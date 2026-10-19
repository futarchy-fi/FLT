/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluIdentity

/-!
# Integral Vélu sums for odd kernels

Pairing inverse points removes the denominators in the defining half-sums.
Consequently integral kernel abscissae and integral source coefficients give
integral target coefficients, including at residue characteristic two.
-/

@[expose] public section

namespace WeierstrassCurve.Velu

variable {K : Type*} [Field K] [DecidableEq K] [NeZero (2 : K)]
variable (E : WeierstrassCurve K) (G : AddSubgroup E.toAffine.Point) [Fintype G]
variable (hodd : ∀ Q : G, Q ≠ 0 → Q ≠ -Q) (S : Subring K)

omit [NeZero (2 : K)] in
/-- Integrality on nonzero kernel points implies integrality on their distinct abscissae. -/
theorem kernelAbscissae_mem (hx : ∀ Q : G, Q ≠ 0 → xCoord Q.val ∈ S)
    {u : K} (hu : u ∈ kernelAbscissae E G) : u ∈ S := by
  classical
  obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hu
  exact hx Q (Finset.mem_erase.mp hQ).1

include hodd

/-- The first paired coefficient sum lies in any subring containing its inputs. -/
theorem t_mem_subring (h₂ : E.b₂ ∈ S) (h₄ : E.b₄ ∈ S)
    (hx : ∀ Q : G, Q ≠ 0 → xCoord Q.val ∈ S) : t E G ∈ S := by
  rw [t_eq_sum_abscissae E G hodd]
  apply S.sum_mem
  intro u hu
  have huS := kernelAbscissae_mem E G S hx hu
  exact S.add_mem (S.add_mem (S.mul_mem (natCast_mem S 6) (S.pow_mem huS 2))
    (S.mul_mem h₂ huS)) h₄

/-- The second paired coefficient sum is integral without inverting two. -/
theorem w_mem_subring (h₂ : E.b₂ ∈ S) (h₄ : E.b₄ ∈ S) (h₆ : E.b₆ ∈ S)
    (hx : ∀ Q : G, Q ≠ 0 → xCoord Q.val ∈ S) : w E G ∈ S := by
  rw [w_eq_sum_abscissae E G hodd]
  apply S.sum_mem
  intro u hu
  have huS := kernelAbscissae_mem E G S hx hu
  have ht := S.add_mem (S.add_mem (S.mul_mem (natCast_mem S 6) (S.pow_mem huS 2))
    (S.mul_mem h₂ huS)) h₄
  exact S.add_mem (S.mul_mem ht huS)
    (S.add_mem (S.add_mem (S.add_mem (S.mul_mem (natCast_mem S 4) (S.pow_mem huS 3))
      (S.mul_mem h₂ (S.pow_mem huS 2)))
      (S.mul_mem (S.mul_mem (natCast_mem S 2) h₄) huS)) h₆)

/-- Integral source coefficients and nonzero kernel abscissae give an integral target. -/
theorem curve_coefficients_mem_subring
    (h₁ : E.a₁ ∈ S) (h₂ : E.a₂ ∈ S) (h₃ : E.a₃ ∈ S)
    (h₄ : E.a₄ ∈ S) (h₆ : E.a₆ ∈ S)
    (hx : ∀ Q : G, Q ≠ 0 → xCoord Q.val ∈ S) :
    (curve E G).a₁ ∈ S ∧ (curve E G).a₂ ∈ S ∧ (curve E G).a₃ ∈ S ∧
      (curve E G).a₄ ∈ S ∧ (curve E G).a₆ ∈ S := by
  have hb₂ : E.b₂ ∈ S := S.add_mem (S.pow_mem h₁ 2) (S.mul_mem (natCast_mem S 4) h₂)
  have hb₄ : E.b₄ ∈ S := S.add_mem (S.mul_mem (natCast_mem S 2) h₄) (S.mul_mem h₁ h₃)
  have hb₆ : E.b₆ ∈ S := S.add_mem (S.pow_mem h₃ 2) (S.mul_mem (natCast_mem S 4) h₆)
  have ht := t_mem_subring E G hodd S hb₂ hb₄ hx
  have hw := w_mem_subring E G hodd S hb₂ hb₄ hb₆ hx
  exact ⟨h₁, h₂, h₃, S.sub_mem h₄ (S.mul_mem (natCast_mem S 5) ht),
    S.sub_mem (S.sub_mem h₆ (S.mul_mem hb₂ ht)) (S.mul_mem (natCast_mem S 7) hw)⟩

end WeierstrassCurve.Velu
