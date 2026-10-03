/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.ContinuousCohomologyColimit
public import FLT.GaloisRepresentation.Extensions.ContinuousClass

/-!
# Integral continuous cochains in degrees zero and one

The coordinate maps use the actual inhomogeneous differential. They identify
one-cocycles and principal cocycles over any commutative ring, including Z.
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

/-- A continuous function in the degree-one term of the actual complex. -/
def continuousOneCochain (c : C(G, M)) : (K).X 1 :=
  ⟨fun x => c (x 0), c.continuous.comp (continuous_apply 0)⟩

/-- Recover the explicit function from a degree-one cochain. -/
def continuousOneFunction (c : (K).X 1) : C(G, M) :=
  ⟨fun g => c.val (fun _ => g), c.property.comp (continuous_pi fun _ => continuous_id)⟩

/-- Degree-one coordinates retain every continuous cochain. -/
theorem continuousOneCochain_function (c : (K).X 1) :
    continuousOneCochain (continuousOneFunction c) = c := by
  apply Subtype.ext
  funext x
  change c.val (fun _ => x 0) = c.val x
  apply congrArg c.val
  funext i
  exact congrArg x (Subsingleton.elim 0 i)

/-- The degree-zero differential is the principal crossed homomorphism. -/
theorem continuous_d_zero (b : (K).X 0) (g : G) :
    (((K).d 0 1).hom b).val (fun _ => g) = g • b.val default - b.val default := by
  exact (congrArg (fun f : (inhomogeneousCochains R).X 0 ⟶ ModuleCat.of k (G → M) =>
    f.hom b.val g) (comp_d₀₁_eq R)).symm

/-- The degree-one differential agrees with the explicit crossed-homomorphism formula. -/
theorem continuous_d_one (b : (K).X 1) (g h : G) :
    (((K).d 1 2).hom b).val ![g, h] =
      g • continuousOneFunction b h - continuousOneFunction b (g * h) +
        continuousOneFunction b g := by
  exact (congrArg (fun f : (inhomogeneousCochains R).X 1 ⟶ ModuleCat.of k (G × G → M) =>
    f.hom b.val (g, h)) (comp_d₁₂_eq R)).symm

/-- The categorical cycle condition is exactly the explicit one-cocycle equation. -/
theorem continuousOneCochain_cycle_iff (c : C(G, M)) :
    ((K).d 1 2).hom (continuousOneCochain c) = 0 ↔ IsCocycle₁ c := by
  constructor
  · intro hc g h
    have he := congrArg (fun f : (K).X 2 => f.val ![g, h]) hc
    rw [continuous_d_one] at he
    change g • c h - c (g * h) + c g = 0 at he
    have he' : g • c h + c g - c (g * h) = 0 := by simpa only [sub_add_eq_add_sub] using he
    exact (sub_eq_zero.mp he').symm
  · intro hc
    apply Subtype.ext
    funext x
    have hx : x = ![x 0, x 1] := by ext i; fin_cases i <;> rfl
    rw [hx, continuous_d_one]
    change x 0 • c (x 1) - c (x 0 * x 1) + c (x 0) = 0
    rw [hc]
    abel

/-- An explicit continuous one-cocycle determines its actual cohomology class. -/
def integralH1Class (c : ContinuousCocycle G M) : continuousCohomology k G M 1 :=
  cochainHomologyClass K 1 (continuousOneCochain c.val)
    (by
      rw [(ComplexShape.up ℕ).next_eq' (show (ComplexShape.up ℕ).Rel 1 2 from rfl)]
      exact (continuousOneCochain_cycle_iff (k := k) c.val).mpr c.property)

/-- Vanishing means a principal cocycle with a coefficient witness. -/
theorem integralH1Class_eq_zero (c : ContinuousCocycle G M) :
    integralH1Class (k := k) c = 0 ↔ ∃ a : M, ∀ g, c.val g = g • a - a := by
  rw [integralH1Class, cochainHomologyClass_eq_zero_iff,
    (ComplexShape.up ℕ).prev_eq' (show (ComplexShape.up ℕ).Rel 0 1 from rfl)]
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨b.val default, fun g => ?_⟩
    have h := congrArg (fun f : (K).X 1 => f.val (fun _ => g)) hb
    exact (continuous_d_zero b g).symm.trans h |>.symm
  · rintro ⟨a, ha⟩
    refine ⟨⟨fun _ => a, continuous_const⟩, ?_⟩
    apply Subtype.ext
    funext x
    have hx : x = fun _ => x 0 := by ext i; congr 1; exact Subsingleton.elim i 0
    rw [hx, continuous_d_zero]
    exact (ha (x 0)).symm

/-- Every categorical H1 class has an explicit continuous crossed homomorphism. -/
theorem integralH1Class_surjective (x : continuousCohomology k G M 1) :
    ∃ c : ContinuousCocycle G M, integralH1Class c = x := by
  obtain ⟨z, hz, rfl⟩ := cochainHomologyClass_surjective K 1 x
  have hc : IsCocycle₁ (continuousOneFunction z) :=
    (continuousOneCochain_cycle_iff _).mp (by
      rw [continuousOneCochain_function]
      convert hz using 1
      exact (congrArg (fun j => ((K).d 1 j).hom z = 0)
        ((ComplexShape.up ℕ).next_eq' (show (ComplexShape.up ℕ).Rel 1 2 from rfl)).symm).to_iff)
  refine ⟨⟨continuousOneFunction z, hc⟩, ?_⟩
  simp only [integralH1Class, continuousOneCochain_function]

end LocalClassFieldTheory
