/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.IntegralDegreeTwoComparison

/-!
# Low-degree cups in the continuous integral complex

Right cup with a trivial scalar character is defined over any commutative
ring. The degree-one differential identity fixes the sign needed for boundaries.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

namespace LocalClassFieldTheory

open CategoryTheory GaloisRepresentation.Extensions

/-- A continuous additive scalar character, without a field hypothesis. -/
abbrev ContinuousScalarCharacter (G k : Type u) [Group G] [AddCommGroup k]
    [TopologicalSpace G] [TopologicalSpace k] :=
  {d : C(G, k) // ∀ g h : G, d (g * h) = d g + d h}

variable {r k G M : Type u} [CommRing r] [CommRing k] [Group G]
  [TopologicalSpace k] [DiscreteTopology k]
  [AddCommGroup M] [Module r M] [Module k M] [DistribMulAction G M]
  [SMulCommClass G r M] [SMulCommClass G k M]
  [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul G M]

local notation "K" => continuousCochains r G M

/-- Right cup of a continuous one-cochain with a trivial scalar character. -/
def integralCupOne (c : (K).X 1) (d : ContinuousScalarCharacter G k) : (K).X 2 :=
  continuousTwoCochain ⟨fun z => d.val z.2 • continuousOneFunction c z.1,
    (continuous_of_discreteTopology (f := fun z : k × M => z.1 • z.2)).comp
      ((d.val.continuous.comp continuous_snd).prodMk
        ((continuousOneFunction c).continuous.comp continuous_fst))⟩

/-- Right cup of a continuous two-cochain with a trivial scalar character. -/
def integralCupTwo (c : (K).X 2) (d : ContinuousScalarCharacter G k) : (K).X 3 :=
  ⟨fun x => d.val (x 2) • continuousTwoFunction c (x 0, x 1),
    (continuous_of_discreteTopology (f := fun z : k × M => z.1 • z.2)).comp
      ((d.val.continuous.comp (continuous_apply 2)).prodMk
        ((continuousTwoFunction c).continuous.comp
          ((continuous_apply 0).prodMk (continuous_apply 1))))⟩

/-- The right character is closed, so the differential acts only on the left factor. -/
theorem integralCupOne_d (c : (K).X 1) (d : ContinuousScalarCharacter G k) :
    ((K).d 2 3).hom (integralCupOne c d) = integralCupTwo (((K).d 1 2).hom c) d := by
  apply Subtype.ext
  funext x
  have hx : x = ![x 0, x 1, x 2] := by ext i; fin_cases i <;> rfl
  rw [hx, continuous_d_two]
  change x 0 • (d.val (x 2) • continuousOneFunction c (x 1)) -
    d.val (x 2) • continuousOneFunction c (x 0 * x 1) +
    d.val (x 1 * x 2) • continuousOneFunction c (x 0) -
    d.val (x 1) • continuousOneFunction c (x 0) =
    d.val (x 2) • ((((K).d 1 2).hom c).val ![x 0, x 1])
  rw [continuous_d_one, d.property, smul_add, smul_sub, add_smul, smul_comm (x 0)]
  abel

omit [SMulCommClass G k M] in
/-- Cup with the zero two-cochain is zero. -/
theorem integralCupTwo_zero (d : ContinuousScalarCharacter G k) :
    integralCupTwo (0 : (K).X 2) d = 0 := by
  apply Subtype.ext
  funext x
  exact smul_zero _

/-- A one-cocycle cups to a genuine cycle in the continuous integral complex. -/
theorem integralCupOne_cycle (c : (K).X 1) (hc : ((K).d 1 2).hom c = 0)
    (d : ContinuousScalarCharacter G k) : ((K).d 2 3).hom (integralCupOne c d) = 0 := by
  rw [integralCupOne_d, hc, integralCupTwo_zero]

/-- The cup class is taken in the actual continuous cochain complex. -/
def integralCupClass (c : ContinuousCocycle G M) (d : ContinuousScalarCharacter G k) :
    continuousCohomology r G M 2 :=
  cochainHomologyClass K 2 (integralCupOne (continuousOneCochain c.val) d)
    (by
      rw [(ComplexShape.up ℕ).next_eq' (show (ComplexShape.up ℕ).Rel 2 3 from rfl)]
      exact integralCupOne_cycle _ ((continuousOneCochain_cycle_iff c.val).mpr c.property) d)

end LocalClassFieldTheory
