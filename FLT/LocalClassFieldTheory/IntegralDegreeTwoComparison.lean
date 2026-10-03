/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.IntegralLowDegreeComparison
public import FLT.GaloisRepresentation.Extensions.ContinuousCup

/-!
# Integral continuous cohomology in degree two

Explicit jointly continuous two-cocycles represent the actual degree-two
cohomology, with vanishing detected by continuous one-cochain witnesses.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

namespace LocalClassFieldTheory

open CategoryTheory groupCohomology GaloisRepresentation.Extensions

variable {k G M : Type u} [CommRing k] [Group G]
  [AddCommGroup M] [Module k M] [DistribMulAction G M] [SMulCommClass G k M]
  [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul G M]

local notation "K" => continuousCochains k G M
local notation "R" => Rep.of (Representation.ofDistribMulAction k G M)

/-- Jointly continuous functions in the degree-two term of the actual complex. -/
def continuousTwoCochain (c : C(G × G, M)) : (K).X 2 :=
  ⟨fun x => c (x 0, x 1), c.continuous.comp
    ((continuous_apply 0).prodMk (continuous_apply 1))⟩

/-- Recover the explicit jointly continuous function. -/
def continuousTwoFunction (c : (K).X 2) : C(G × G, M) :=
  ⟨fun z => c.val ![z.1, z.2], c.property.comp
    (continuous_pi fun i => by fin_cases i <;> fun_prop)⟩

/-- Degree-two coordinates retain every continuous cochain. -/
theorem continuousTwoCochain_function (c : (K).X 2) :
    continuousTwoCochain (continuousTwoFunction c) = c := by
  apply Subtype.ext
  funext x
  change c.val ![x 0, x 1] = c.val x
  apply congrArg c.val
  ext i
  fin_cases i <;> rfl

/-- The differential in degree two is the usual explicit two-cocycle equation. -/
theorem continuous_d_two (b : (K).X 2) (g h j : G) :
    (((K).d 2 3).hom b).val ![g, h, j] =
      g • continuousTwoFunction b (h, j) - continuousTwoFunction b (g * h, j) +
        continuousTwoFunction b (g, h * j) - continuousTwoFunction b (g, h) := by
  exact (congrArg (fun f : (inhomogeneousCochains R).X 2 ⟶
    ModuleCat.of k (G × G × G → M) => f.hom b.val (g, h, j)) (comp_d₂₃_eq R)).symm

/-- The degree-two cycle condition agrees with the existing explicit presentation. -/
theorem continuousTwoCochain_cycle_iff (c : C(G × G, M)) :
    ((K).d 2 3).hom (continuousTwoCochain c) = 0 ↔ IsCocycle₂ c := by
  constructor
  · intro hc g h j
    have he := congrArg (fun f : (K).X 3 => f.val ![g, h, j]) hc
    rw [continuous_d_two] at he
    change g • c (h, j) - c (g * h, j) + c (g, h * j) - c (g, h) = 0 at he
    change c (g * h, j) + c (g, h) = g • c (h, j) + c (g, h * j)
    apply (sub_eq_zero.mp ?_).symm
    convert he using 1; abel
  · intro hc
    apply Subtype.ext
    funext x
    have hx : x = ![x 0, x 1, x 2] := by ext i; fin_cases i <;> rfl
    rw [hx, continuous_d_two]
    change x 0 • c (x 1, x 2) - c (x 0 * x 1, x 2) +
      c (x 0, x 1 * x 2) - c (x 0, x 1) = 0
    have h := hc (x 0) (x 1) (x 2)
    rw [← sub_eq_zero] at h
    convert congrArg Neg.neg h using 1 <;> abel

/-- The actual cohomology class of an explicit continuous two-cocycle. -/
def integralH2Class (c : C(G × G, M)) (hc : IsCocycle₂ c) : continuousCohomology k G M 2 :=
  cochainHomologyClass K 2 (continuousTwoCochain c)
    (by
      rw [(ComplexShape.up ℕ).next_eq' (show (ComplexShape.up ℕ).Rel 2 3 from rfl)]
      exact (continuousTwoCochain_cycle_iff (k := k) c).mpr hc)

/-- Vanishing is equivalent to an actual continuous one-cochain boundary. -/
theorem integralH2Class_eq_zero (c : C(G × G, M)) (hc : IsCocycle₂ c) :
    integralH2Class (k := k) c hc = 0 ↔ ContinuousIsCoboundaryTwo c := by
  rw [integralH2Class, cochainHomologyClass_eq_zero_iff,
    (ComplexShape.up ℕ).prev_eq' (show (ComplexShape.up ℕ).Rel 1 2 from rfl)]
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨continuousOneFunction b, fun g h => ?_⟩
    have he := congrArg (fun f : (K).X 2 => f.val ![g, h]) hb
    exact (continuous_d_one b g h).symm.trans he
  · rintro ⟨b, hb⟩
    refine ⟨continuousOneCochain b, ?_⟩
    apply Subtype.ext
    funext x
    have hx : x = ![x 0, x 1] := by ext i; fin_cases i <;> rfl
    rw [hx, continuous_d_one]
    exact hb (x 0) (x 1)

/-- Every categorical H2 class has an explicit jointly continuous cocycle. -/
theorem integralH2Class_surjective (x : continuousCohomology k G M 2) :
    ∃ (c : C(G × G, M)) (hc : IsCocycle₂ c), integralH2Class c hc = x := by
  obtain ⟨z, hz, rfl⟩ := cochainHomologyClass_surjective K 2 x
  have hc : IsCocycle₂ (continuousTwoFunction z) :=
    (continuousTwoCochain_cycle_iff _).mp (by
      rw [continuousTwoCochain_function]
      convert hz using 1
      exact (congrArg (fun j => ((K).d 2 j).hom z = 0)
        ((ComplexShape.up ℕ).next_eq' (show (ComplexShape.up ℕ).Rel 2 3 from rfl)).symm).to_iff)
  refine ⟨continuousTwoFunction z, hc, ?_⟩
  simp only [integralH2Class, continuousTwoCochain_function]

end LocalClassFieldTheory
