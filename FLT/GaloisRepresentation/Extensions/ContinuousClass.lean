/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.Extensions.ChangeSplitting

/-!
# Explicit continuous cocycle classes

Continuous crossed homomorphisms modulo changes of splitting admit injective
inflation along a continuous surjection. This is an explicit quotient; no
comparison with the derived continuous cohomology functor is asserted here.
-/

@[expose] public section

namespace GaloisRepresentation.Extensions

variable (G M : Type*) [Group G] [AddCommGroup M] [DistribMulAction G M]
    [TopologicalSpace G] [TopologicalSpace M]

/-- Continuous crossed homomorphisms for an additive coefficient action. -/
abbrev ContinuousCocycle := {c : C(G, M) // groupCohomology.IsCocycle₁ c}

/-- The equivalence relation on continuous cocycles given by splitting changes. -/
def continuousCocycleSetoid : Setoid (ContinuousCocycle G M) where
  r c d := SplittingEquivalent (fun g ↦ c.1 g) (fun g ↦ d.1 g)
  iseqv :=
    ⟨fun _ ↦ splittingEquivalent_equivalence.refl _,
      fun h ↦ splittingEquivalent_equivalence.symm h,
      fun h₁ h₂ ↦ splittingEquivalent_equivalence.trans h₁ h₂⟩

/-- Explicit continuous degree-one classes, with no derived-functor identification. -/
def ContinuousClass := Quotient (continuousCocycleSetoid G M)

variable {G M}

/-- The class of a continuous cocycle. -/
def continuousClassMk (c : ContinuousCocycle G M) : ContinuousClass G M :=
  Quotient.mk _ c

/-- Equality of classes is exactly change of splitting. -/
theorem continuousClassMk_eq_iff (c d : ContinuousCocycle G M) :
    continuousClassMk c = continuousClassMk d ↔
      SplittingEquivalent (fun g ↦ c.1 g) (fun g ↦ d.1 g) := Quotient.eq

variable {Q : Type*} [Group Q] [TopologicalSpace Q] [DistribMulAction Q M]
    (π : G →* Q) (hπ : Continuous π)
    (hact : ∀ (g : G) (x : M), g • x = π g • x)

/-- Inflate a continuous cocycle along a continuous map of acting groups. -/
def inflateCocycle (c : ContinuousCocycle Q M) : ContinuousCocycle G M :=
  ⟨⟨fun g ↦ c.1 (π g), c.1.continuous.comp hπ⟩, fun g h ↦ by
    simpa only [ContinuousMap.coe_mk, map_mul, hact] using c.2 (π g) (π h)⟩

/-- Inflation respects a change of splitting. -/
theorem inflateCocycle_equivalent {c d : ContinuousCocycle Q M}
    (h : SplittingEquivalent (fun q ↦ c.1 q) (fun q ↦ d.1 q)) :
    SplittingEquivalent (fun g ↦ (inflateCocycle π hπ hact c).1 g)
      (fun g ↦ (inflateCocycle π hπ hact d).1 g) := by
  obtain ⟨a, ha⟩ := h
  refine ⟨a, funext fun g ↦ ?_⟩
  simpa only [inflateCocycle, ContinuousMap.coe_mk, changeSplitting, hact] using congrFun ha (π g)

/-- Surjectivity detects changes of splitting after inflation. -/
theorem inflateCocycle_equivalent_iff (hsurj : Function.Surjective π)
    (c d : ContinuousCocycle Q M) :
    SplittingEquivalent (fun g ↦ (inflateCocycle π hπ hact c).1 g)
      (fun g ↦ (inflateCocycle π hπ hact d).1 g) ↔
        SplittingEquivalent (fun q ↦ c.1 q) (fun q ↦ d.1 q) := by
  refine ⟨?_, inflateCocycle_equivalent π hπ hact⟩
  rintro ⟨a, ha⟩
  refine ⟨a, funext fun q ↦ ?_⟩
  obtain ⟨g, rfl⟩ := hsurj q
  simpa only [inflateCocycle, ContinuousMap.coe_mk, changeSplitting, hact] using congrFun ha g

/-- Inflation of explicit continuous cohomology classes. -/
def inflateClass : ContinuousClass Q M → ContinuousClass G M :=
  Quotient.map (inflateCocycle π hπ hact) (fun _ _ ↦ inflateCocycle_equivalent π hπ hact)

/-- Inflation along a surjection is injective on continuous classes. -/
theorem inflateClass_injective (hsurj : Function.Surjective π) :
    Function.Injective (inflateClass π hπ hact) := by
  intro x y
  induction x using Quotient.inductionOn with | h c =>
    induction y using Quotient.inductionOn with | h d =>
      intro h
      exact Quotient.sound ((inflateCocycle_equivalent_iff π hπ hact hsurj c d).mp
        (Quotient.exact h))

end GaloisRepresentation.Extensions
