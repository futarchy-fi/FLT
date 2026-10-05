/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticTypeIVStarCoordinates
public import FLT.Mazur.EllipticTypeIVScaledComparison
public import FLT.Mazur.EllipticNormalizedTypeIV

/-!
# The normalized type IV* rational component bound

For coefficient depths (1,2,2,3,4) and b₆ outside m⁵, every actual point
outside E₀ has coordinates divided by π². The residual y-quadratic has
distinct roots, so its classes are equal or opposite and E/E₀ has at most
three elements. No splitting or perfectness hypothesis is used.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve IsLocalRing

variable {K : Type*} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)
  {π : A} (hπ : π ≠ 0) (hgen : maximalIdeal A = Ideal.span {π})
  (h1 : W.a₁ ∈ maximalIdeal A) (h2 : W.a₂ ∈ maximalIdeal A ^ 2)
  (h3 : W.a₃ ∈ maximalIdeal A ^ 2) (h4 : W.a₄ ∈ maximalIdeal A ^ 3)
  (h6 : W.a₆ ∈ maximalIdeal A ^ 4) (hb6 : W.b₆ ∉ maximalIdeal A ^ 5)

include hπ hgen h1 h2 h3 h4 h6 hb6

/-- Actual nonzero components in the normalized type IV* branch are equal or opposite. -/
theorem component_eq_or_neg_of_normalizedTypeIVStar (c d : EllipticComponentQuotient A W)
    (hc : c ≠ 0) (hd : d ≠ 0) : c = d ∨ c = -d := by
  obtain ⟨P, rfl⟩ := ellipticComponentHom_surjective A W c
  obtain ⟨Q, rfl⟩ := ellipticComponentHom_surjective A W d
  obtain ⟨v⟩ := exists_typeIVStarCoordinates A W hπ hgen h1 h2 h3 h4 h6 P
    (fun h => hc ((ellipticComponentHom_eq_zero A W P).mpr h))
  obtain ⟨w⟩ := exists_typeIVStarCoordinates A W hπ hgen h1 h2 h3 h4 h6 Q
    (fun h => hd ((ellipticComponentHom_eq_zero A W Q).mpr h))
  obtain ⟨e3, he3⟩ := exists_node_coordinate_factor hgen 2 h3
  obtain ⟨e4, he4m, he4⟩ := exists_node_deep_factor hgen 2 h4
  obtain ⟨e6, he6⟩ := exists_node_coordinate_factor hgen 4 h6
  have hπm : π ∈ maximalIdeal A := hgen ▸ Ideal.mem_span_singleton_self π
  have hs : π ^ 2 ∈ maximalIdeal A :=
    Ideal.pow_le_self (by decide : 2 ≠ 0) (Ideal.pow_mem_pow hπm 2)
  exact v.component_eq_or_neg_of_residue_discr w (pow_ne_zero 2 hπ) hs e3 e4 e6
    h1 (Ideal.pow_le_self (by decide : 2 ≠ 0) h2) he4m he3 he4
    (by simpa only [← pow_mul] using he6)
    (typeIVStar_residue_discriminant_ne_zero W hπm e3 e6 he3 he6 hb6)

/-- The normalized type IV* quotient is finite and has at most three elements. -/
theorem normalizedTypeIVStar_components :
    Finite (EllipticComponentQuotient A W) ∧ Nat.card (EllipticComponentQuotient A W) ≤ 3 :=
  finite_card_le_three_of_eq_or_neg
    (component_eq_or_neg_of_normalizedTypeIVStar A W hπ hgen h1 h2 h3 h4 h6 hb6)

end FLT.Mazur
