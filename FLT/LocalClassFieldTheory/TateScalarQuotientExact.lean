/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.AbelianizationQuotientExact
public import FLT.LocalClassFieldTheory.TateScalarMap

/-!
# Exactness of scalar Tate groups at a group quotient

The canonical abelianization comparison transports quotient exactness to
the actual Tate groups in degree minus two.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

variable {G : Type} [Group G] [Fintype G]
  (N : Subgroup G) [N.Normal] [Fintype N] [Fintype (G ⧸ N)]

omit [Fintype N] in
/-- The scalar Tate map of a group quotient is surjective. -/
theorem tateScalarMap_quotient_surjective :
    Function.Surjective (tateScalarMap (QuotientGroup.mk' N)) := by
  intro x
  obtain ⟨q, rfl⟩ := tateScalarGenerator_surjective (G ⧸ N) x
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N q
  exact ⟨tateScalarGenerator ℤ G g, tateScalarMap_generator _ _⟩

/-- The scalar quotient kernel is precisely the image from the subgroup. -/
theorem tateScalarMap_quotient_eq_zero_iff
    (x : tateCohomology (Rep.trivial ℤ G ℤ) (-2)) :
    tateScalarMap (QuotientGroup.mk' N) x = 0 ↔
      ∃ y : tateCohomology (Rep.trivial ℤ N ℤ) (-2), tateScalarMap N.subtype y = x := by
  constructor
  · intro hx
    have ha : Abelianization.map (QuotientGroup.mk' N)
        (Additive.toMul (tateScalarAbelianizationEquiv G x)) = 1 := by
      have h := congrArg (tateScalarAbelianizationEquiv (G ⧸ N)) hx
      simpa [tateScalarMap] using h
    obtain ⟨b, hb⟩ := (abelianization_quotient_eq_one_iff N _).mp ha
    refine ⟨(tateScalarAbelianizationEquiv N).symm (Additive.ofMul b), ?_⟩
    apply (tateScalarAbelianizationEquiv G).injective
    simpa [tateScalarMap] using congrArg Additive.ofMul hb
  · rintro ⟨y, rfl⟩
    obtain ⟨n, rfl⟩ := tateScalarGenerator_surjective N y
    rw [tateScalarMap_generator, tateScalarMap_generator]
    apply (tateScalarAbelianizationEquiv (G ⧸ N)).injective
    rw [tateScalarAbelianizationEquiv_generator, map_zero]
    have hn : QuotientGroup.mk' N (n : G) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr n.property
    simp [hn]

end LocalClassFieldTheory
