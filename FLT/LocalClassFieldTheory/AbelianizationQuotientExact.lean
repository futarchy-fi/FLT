/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.GroupTheory.Abelianization.Defs

/-!
# Exactness of abelianization at a group quotient

The kernel of the actual map to the quotient's abelianization is precisely
the image of the normal subgroup's abelianization.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

variable {G : Type} [Group G] (N : Subgroup G) [N.Normal]

/-- Abelianization preserves surjectivity of a quotient map. -/
theorem abelianization_quotient_surjective :
    Function.Surjective (Abelianization.map (QuotientGroup.mk' N)) := by
  intro b
  refine QuotientGroup.induction_on b ?_
  intro q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N q
  exact ⟨Abelianization.of g, rfl⟩

/-- The quotient kernel is the image of the subgroup's actual abelianization map. -/
theorem abelianization_quotient_eq_one_iff (a : Abelianization G) :
    Abelianization.map (QuotientGroup.mk' N) a = 1 ↔
      ∃ b : Abelianization N, Abelianization.map N.subtype b = a := by
  refine QuotientGroup.induction_on a ?_
  intro g
  change Abelianization.of (QuotientGroup.mk' N g) = 1 ↔ _
  constructor
  · intro h
    have hc : QuotientGroup.mk' N g ∈ commutator (G ⧸ N) :=
      (QuotientGroup.eq_one_iff _).mp h
    have hm : (commutator G).map (QuotientGroup.mk' N) = commutator (G ⧸ N) := by
      rw [map_commutator_eq, MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective N)]
      rfl
    rw [← hm] at hc
    obtain ⟨c, hc, hcg⟩ := hc
    let n : N := ⟨g * c⁻¹, by
      apply (QuotientGroup.eq_one_iff _).mp
      change QuotientGroup.mk' N (g * c⁻¹) = 1
      rw [map_mul, map_inv, hcg, mul_inv_cancel]⟩
    refine ⟨Abelianization.of n, ?_⟩
    change Abelianization.of (g * c⁻¹) = Abelianization.of g
    have hz : Abelianization.of c = 1 := (QuotientGroup.eq_one_iff c).mpr hc
    rw [map_mul, map_inv, hz, inv_one, mul_one]
  · rintro ⟨b, hb⟩
    change Abelianization.map N.subtype b = Abelianization.of g at hb
    rw [← Abelianization.map_of, ← hb, Abelianization.map_map_apply]
    refine QuotientGroup.induction_on b ?_
    intro n
    change Abelianization.of (QuotientGroup.mk' N (n : G)) = 1
    rw [show QuotientGroup.mk' N (n : G) = 1 from
      (QuotientGroup.eq_one_iff _).mpr n.property, map_one]

end LocalClassFieldTheory
