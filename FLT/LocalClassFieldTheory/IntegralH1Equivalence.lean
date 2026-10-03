/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.IntegralLowDegreeComparison

/-!
# The explicit splitting quotient equals integral continuous H1

Equality of categorical classes is exactly change of splitting. This gives
an equivalence with the pre-existing explicit quotient, also over Z.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

namespace LocalClassFieldTheory

open CategoryTheory GaloisRepresentation.Extensions

/-- Subtraction of representatives agrees with subtraction of categorical homology classes. -/
theorem cochainHomologyClass_sub {k : Type u} [CommRing k]
    (K : CochainComplex (ModuleCat.{u} k) ℕ) (n : ℕ) (c d : K.X n)
    (hc : (K.d n ((ComplexShape.up ℕ).next n)).hom c = 0)
    (hd : (K.d n ((ComplexShape.up ℕ).next n)).hom d = 0)
    (hcd : (K.d n ((ComplexShape.up ℕ).next n)).hom (c - d) = 0) :
    cochainHomologyClass K n (c - d) hcd =
      cochainHomologyClass K n c hc - cochainHomologyClass K n d hd := by
  unfold cochainHomologyClass
  rw [← map_sub]
  apply congrArg (K.homologyπ n).hom
  apply (ModuleCat.mono_iff_injective (K.iCycles n)).mp inferInstance
  simp only [map_sub, cochainCyclesMk_val]

variable {k G M : Type u} [CommRing k] [Group G]
  [AddCommGroup M] [Module k M] [DistribMulAction G M] [SMulCommClass G k M]
  [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul G M]

/-- The difference of two explicit continuous crossed homomorphisms. -/
def integralCocycleSub (c d : ContinuousCocycle G M) : ContinuousCocycle G M :=
  ⟨⟨fun g => c.val g - d.val g, c.val.continuous.sub d.val.continuous⟩, fun g h => by
    change c.val (g * h) - d.val (g * h) = g • (c.val h - d.val h) + (c.val g - d.val g)
    rw [c.property, d.property, smul_sub]
    abel⟩

/-- The integral comparison preserves differences of explicit cocycles. -/
theorem integralH1Class_sub (c d : ContinuousCocycle G M) :
    integralH1Class (k := k) (integralCocycleSub c d) = integralH1Class c - integralH1Class d := by
  unfold integralH1Class
  exact cochainHomologyClass_sub (continuousCochains k G M) 1
    (continuousOneCochain c.val) (continuousOneCochain d.val) _ _ _

/-- Categorical equality is exactly the existing splitting equivalence. -/
theorem integralH1Class_eq_iff (c d : ContinuousCocycle G M) :
    integralH1Class (k := k) c = integralH1Class d ↔
      SplittingEquivalent (fun g => c.val g) (fun g => d.val g) := by
  rw [eq_comm, ← sub_eq_zero, ← integralH1Class_sub, integralH1Class_eq_zero,
    splittingEquivalent_iff_coboundary]
  simp only [integralCocycleSub, groupCohomology.IsCoboundary₁, ContinuousMap.coe_mk, eq_comm]

/-- The comparison descends to the existing explicit quotient. -/
def integralH1Comparison : ContinuousClass G M → continuousCohomology k G M 1 :=
  Quotient.lift integralH1Class (fun c d h => (integralH1Class_eq_iff c d).mpr h)

/-- Passing to the splitting quotient loses no categorical information. -/
theorem integralH1Comparison_injective :
    Function.Injective (integralH1Comparison (k := k) (G := G) (M := M)) := by
  intro x y
  induction x using Quotient.inductionOn with | h c =>
    induction y using Quotient.inductionOn with | h d =>
      intro h
      exact Quotient.sound ((integralH1Class_eq_iff c d).mp h)

/-- Every categorical class comes from the existing splitting quotient. -/
theorem integralH1Comparison_surjective :
    Function.Surjective (integralH1Comparison (k := k) (G := G) (M := M)) := by
  intro x
  obtain ⟨c, hc⟩ := integralH1Class_surjective x
  exact ⟨continuousClassMk c, hc⟩

/-- The actual integral complex computes the previously defined explicit H1 quotient. -/
def integralH1Equiv : ContinuousClass G M ≃ continuousCohomology k G M 1 :=
  Equiv.ofBijective integralH1Comparison
    ⟨integralH1Comparison_injective, integralH1Comparison_surjective⟩

/-- The equivalence sends a cocycle to its class in the actual complex. -/
theorem integralH1Equiv_mk (c : ContinuousCocycle G M) :
    integralH1Equiv (k := k) (continuousClassMk c) = integralH1Class c := rfl

end LocalClassFieldTheory
