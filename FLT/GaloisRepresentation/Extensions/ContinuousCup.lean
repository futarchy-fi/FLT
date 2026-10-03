/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.Extensions.LinearContinuousClass

/-!
# Continuous cups with trivial dual characters

For a cocycle c and an additive character d, the cup is d(h) • c(g).
A change of splitting changes the cup by an actual continuous coboundary.
These are explicit low-degree cochains, with no local-duality assertion.
-/

@[expose] public section

namespace GaloisRepresentation.Extensions

variable (G k : Type*) [Group G] [TopologicalSpace G] [Field k] [TopologicalSpace k]

/-- A continuous degree-one cocycle with trivial scalar action. -/
abbrev ContinuousAddCharacter := {d : C(G, k) // ∀ g h : G, d (g * h) = d g + d h}

variable {G k} [DiscreteTopology k]
    {M : Type*} [AddCommGroup M] [Module k M] [DistribMulAction G M]
    [SMulCommClass G k M] [TopologicalSpace M] [DiscreteTopology M]

/-- The continuous cup of a degree-one cocycle and a trivial additive character. -/
def continuousCup (c : ContinuousCocycle G M) (d : ContinuousAddCharacter G k) : C(G × G, M) :=
  ⟨fun z ↦ d.1 z.2 • c.1 z.1,
    (continuous_of_discreteTopology (f := fun z : k × M ↦ z.1 • z.2)).comp
      ((d.1.continuous.comp continuous_snd).prodMk (c.1.continuous.comp continuous_fst))⟩

/-- This is a genuine continuous 2-cocycle. -/
theorem continuousCup_isCocycle (c : ContinuousCocycle G M) (d : ContinuousAddCharacter G k) :
    groupCohomology.IsCocycle₂ (continuousCup c d) := by
  intro g h j
  change d.1 j • c.1 (g * h) + d.1 h • c.1 g =
    g • (d.1 j • c.1 h) + d.1 (h * j) • c.1 g
  rw [c.2, d.2, smul_add, add_smul, smul_comm g]
  abel

/-- Vanishing in explicit continuous degree-two cohomology, with a continuous witness. -/
def ContinuousIsCoboundaryTwo (f : C(G × G, M)) : Prop :=
  ∃ b : C(G, M), ∀ g h : G, g • b h - b (g * h) + b g = f (g, h)

/-- Multiplying a trivial character by a fixed coefficient gives a continuous cochain. -/
def splittingCupCochain (d : ContinuousAddCharacter G k) (a : M) : C(G, M) :=
  ⟨fun g ↦ d.1 g • a,
    (continuous_of_discreteTopology (f := fun r : k ↦ r • a)).comp d.1.continuous⟩

/-- A splitting change has an explicit continuous coboundary as its cup difference. -/
theorem continuousCup_splitting_difference (c c' : ContinuousCocycle G M)
    (d : ContinuousAddCharacter G k) (a : M)
    (ha : (fun g ↦ c'.1 g) = changeSplitting (fun g ↦ c.1 g) a) (g h : G) :
    g • splittingCupCochain d a h - splittingCupCochain d a (g * h) +
      splittingCupCochain d a g = continuousCup c' d (g, h) - continuousCup c d (g, h) := by
  change g • (d.1 h • a) - d.1 (g * h) • a + d.1 g • a =
    d.1 h • c'.1 g - d.1 h • c.1 g
  rw [congrFun ha g]
  simp only [changeSplitting, d.2, add_smul, smul_add, smul_sub, smul_comm g]
  abel

/-- Adding an actual continuous coboundary preserves and reflects degree-two vanishing. -/
theorem continuousCoboundaryTwo_difference_iff (f f' : C(G × G, M)) (t : C(G, M))
    (ht : ∀ g h : G, g • t h - t (g * h) + t g = f' (g, h) - f (g, h)) :
    ContinuousIsCoboundaryTwo f' ↔ ContinuousIsCoboundaryTwo f := by
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨b - t, fun g h ↦ ?_⟩
    change g • (b h - t h) - (b (g * h) - t (g * h)) + (b g - t g) = _
    rw [smul_sub]
    have he : g • b h - g • t h - (b (g * h) - t (g * h)) + (b g - t g) =
        (g • b h - b (g * h) + b g) - (g • t h - t (g * h) + t g) := by abel
    rw [he, hb, ht]
    abel
  · rintro ⟨b, hb⟩
    refine ⟨b + t, fun g h ↦ ?_⟩
    change g • (b h + t h) - (b (g * h) + t (g * h)) + (b g + t g) = _
    rw [smul_add]
    have he : g • b h + g • t h - (b (g * h) + t (g * h)) + (b g + t g) =
        (g • b h - b (g * h) + b g) + (g • t h - t (g * h) + t g) := by abel
    rw [he, hb, ht]
    abel

/-- The vanishing cup condition depends only on the continuous splitting class. -/
theorem continuousCup_splitting_iff (c c' : ContinuousCocycle G M)
    (d : ContinuousAddCharacter G k)
    (h : SplittingEquivalent (fun g ↦ c.1 g) (fun g ↦ c'.1 g)) :
    ContinuousIsCoboundaryTwo (continuousCup c' d) ↔
      ContinuousIsCoboundaryTwo (continuousCup c d) := by
  obtain ⟨a, ha⟩ := h
  exact continuousCoboundaryTwo_difference_iff _ _ (splittingCupCochain d a)
    (continuousCup_splitting_difference c c' d a ha)

end GaloisRepresentation.Extensions
