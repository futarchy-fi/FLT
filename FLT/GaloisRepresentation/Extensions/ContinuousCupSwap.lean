/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.Extensions.ContinuousCup

/-!
# Changing the order of a continuous cup

The character-first cup differs by a minus sign and an explicit continuous
coboundary from the cocycle-first cup. This fixes the sign needed to compare
the latter with arithmetic Frobenius normalization of local reciprocity.
-/

@[expose] public section

namespace GaloisRepresentation.Extensions

variable {G k M : Type*} [Group G] [TopologicalSpace G]
    [Field k] [TopologicalSpace k] [DiscreteTopology k]
    [AddCommGroup M] [Module k M] [DistribMulAction G M] [SMulCommClass G k M]
    [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M]

/-- The character-first cup, with the group action on the second coefficient. -/
def continuousOppositeCup (c : ContinuousCocycle G M) (d : ContinuousAddCharacter G k) :
    C(G × G, M) :=
  ⟨fun z ↦ d.1 z.1 • (z.1 • c.1 z.2),
    (continuous_of_discreteTopology (f := fun z : k × M ↦ z.1 • z.2)).comp
      ((d.1.continuous.comp continuous_fst).prodMk
        (continuous_fst.smul (c.1.continuous.comp continuous_snd)))⟩

/-- The character-first cup is a continuous two-cocycle. -/
theorem continuousOppositeCup_isCocycle (c : ContinuousCocycle G M)
    (d : ContinuousAddCharacter G k) :
    groupCohomology.IsCocycle₂ (continuousOppositeCup c d) := by
  intro g h j
  change d.1 (g * h) • ((g * h) • c.1 j) + d.1 g • (g • c.1 h) =
    g • (d.1 h • (h • c.1 j)) + d.1 g • (g • c.1 (h * j))
  rw [d.2, c.2]
  simp only [add_smul, smul_add, mul_smul, smul_comm g]
  abel

/-- The diagonal cochain giving the change-of-order homotopy. -/
def cupSwapCochain (c : ContinuousCocycle G M) (d : ContinuousAddCharacter G k) : C(G, M) :=
  ⟨fun g ↦ d.1 g • c.1 g,
    (continuous_of_discreteTopology (f := fun z : k × M ↦ z.1 • z.2)).comp
      (d.1.continuous.prodMk c.1.continuous)⟩

/-- With differential g b(h) - b(gh) + b(g), the sum of the two cups is minus db. -/
theorem cupSwapCochain_differential (c : ContinuousCocycle G M)
    (d : ContinuousAddCharacter G k) (g h : G) :
    g • cupSwapCochain c d h - cupSwapCochain c d (g * h) + cupSwapCochain c d g =
      -(continuousCup c d (g, h) + continuousOppositeCup c d (g, h)) := by
  change g • (d.1 h • c.1 h) - d.1 (g * h) • c.1 (g * h) + d.1 g • c.1 g =
    -(d.1 h • c.1 g + d.1 g • (g • c.1 h))
  rw [d.2, c.2]
  simp only [add_smul, smul_add, smul_comm g]
  abel

omit [ContinuousSMul G M] in
/-- Negating a continuous coboundary preserves and reflects being a coboundary. -/
theorem continuousIsCoboundaryTwo_neg_iff (f : C(G × G, M)) :
    ContinuousIsCoboundaryTwo (-f) ↔ ContinuousIsCoboundaryTwo f := by
  constructor <;> rintro ⟨b, hb⟩ <;> refine ⟨-b, fun g h ↦ ?_⟩
  · have he := hb g h
    change g • b h - b (g * h) + b g = -f (g, h) at he
    change g • -b h - -b (g * h) + -b g = f (g, h)
    rw [smul_neg]
    calc
      _ = -(g • b h - b (g * h) + b g) := by abel
      _ = f (g, h) := by rw [he, neg_neg]
  · change g • -b h - -b (g * h) + -b g = -f (g, h)
    rw [smul_neg]
    calc
      _ = -(g • b h - b (g * h) + b g) := by abel
      _ = -f (g, h) := by rw [hb]

/-- The annihilator zero test is independent of the order of these degree-one cups. -/
theorem continuousOppositeCup_coboundary_iff (c : ContinuousCocycle G M)
    (d : ContinuousAddCharacter G k) :
    ContinuousIsCoboundaryTwo (continuousOppositeCup c d) ↔
      ContinuousIsCoboundaryTwo (continuousCup c d) := by
  rw [← continuousIsCoboundaryTwo_neg_iff (continuousOppositeCup c d)]
  apply continuousCoboundaryTwo_difference_iff _ _ (cupSwapCochain c d)
  intro g h
  rw [cupSwapCochain_differential]
  change -(_ + _) = -_ - _
  abel

end GaloisRepresentation.Extensions
