/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.CyclicCarry
public import FLT.LocalClassFieldTheory.IntegralCochainCup
public import FLT.LocalClassFieldTheory.IntegralTwoClassAdditive
public import Mathlib.Topology.Instances.ZMod

/-!
# The root-ratio cup and the positive carry

The differential of the lifted-character root cochain is the sum of the
root-ratio-first cup and the positive parameter carry. Thus their classes
have opposite signs. The root equation is used in the cochain calculation.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open groupCohomology GaloisRepresentation.Extensions

variable {G M : Type} [Group G] [AddCommGroup M] [DistribMulAction G M]
  [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul G M] {n : ℕ} [NeZero n]
  (χ : ContinuousScalarCharacter G (ZMod n))

/-- Integer representatives of a finite continuous character give a root-valued cochain. -/
def cyclicRootLift (b : M) : C(G, M) :=
  ⟨fun g => (χ.val g).val • b,
    (continuous_of_discreteTopology (f := fun z : ZMod n => z.val • b)).comp χ.val.continuous⟩

/-- The root-ratio-first cup after inclusion into the ambient coefficient group. -/
def cyclicRootRatioCup (b : M) : C(G × G, M) :=
  ⟨fun z => (χ.val z.2).val • (z.1 • b - b),
    (continuous_of_discreteTopology (f := fun z : ZMod n × M => z.1.val • z.2)).comp
      ((χ.val.continuous.comp continuous_snd).prodMk
        ((continuous_fst.smul continuous_const).sub continuous_const))⟩

/-- The positive carry with coefficients in the base parameter. -/
def cyclicParameterCarry (a : M) : C(G × G, M) :=
  ⟨fun z => cyclicCarry (χ.val z.1) (χ.val z.2) • a,
    (continuous_of_discreteTopology (f := fun z : ZMod n × ZMod n =>
      cyclicCarry z.1 z.2 • a)).comp
      ((χ.val.continuous.comp continuous_fst).prodMk
        (χ.val.continuous.comp continuous_snd))⟩

omit [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
  [DiscreteTopology M] [ContinuousSMul G M] in
/-- A fixed coefficient preserves the carry cocycle equation. -/
theorem cyclicParameterCarry_isCocycle (a : M) (ha : ∀ g : G, g • a = a) :
    IsCocycle₂ (cyclicParameterCarry χ a) := by
  intro g h j
  change cyclicCarry (χ.val (g * h)) (χ.val j) • a +
    cyclicCarry (χ.val g) (χ.val h) • a =
    g • (cyclicCarry (χ.val h) (χ.val j) • a) +
      cyclicCarry (χ.val g) (χ.val (h * j)) • a
  rw [χ.property, χ.property, smul_comm g, ha, ← add_smul, ← add_smul,
    cyclicCarry_cocycle]

omit [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] in
/-- The explicit boundary identity fixes the root-ratio-first cup sign. -/
theorem cyclicRootLift_differential (b : M) (g h : G) :
    g • cyclicRootLift χ b h - cyclicRootLift χ b (g * h) + cyclicRootLift χ b g =
      cyclicRootRatioCup χ b (g, h) + cyclicParameterCarry χ (n • b) (g, h) := by
  change g • ((χ.val h).val • b) - (χ.val (g * h)).val • b + (χ.val g).val • b =
    (χ.val h).val • (g • b - b) + cyclicCarry (χ.val g) (χ.val h) • (n • b)
  rw [χ.property]
  simp only [← Nat.cast_smul_eq_nsmul ℤ, smul_comm g, smul_sub, ← mul_smul,
    cyclicCarry_mul, sub_smul, add_smul]
  abel

omit [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] in
/-- A root of a fixed parameter gives a genuine continuous cup cocycle. -/
theorem cyclicRootRatioCup_isCocycle (b a : M) (hb : n • b = a)
    (ha : ∀ g : G, g • a = a) : IsCocycle₂ (cyclicRootRatioCup χ b) := by
  let A := Rep.of (Representation.ofDistribMulAction ℤ G M)
  have hc := (mem_cocycles₂_iff (A := A) _).mpr (cyclicParameterCarry_isCocycle χ a ha)
  have hd := (cocycles₂ A).sub_mem (d₁₂_apply_mem_cocycles₂ (A := A) (cyclicRootLift χ b)) hc
  apply (mem_cocycles₂_iff (A := A) _).mp
  convert hd using 1
  ext z
  have h := cyclicRootLift_differential χ b z.1 z.2
  rw [hb] at h
  exact eq_sub_iff_add_eq.mpr h.symm

/-- The actual continuous H2 classes have opposite signs, witnessed by the root lift. -/
theorem cyclicRootRatioCup_class (b a : M) (hb : n • b = a)
    (ha : ∀ g : G, g • a = a) :
    integralH2Class (k := ℤ) (cyclicRootRatioCup χ b)
        (cyclicRootRatioCup_isCocycle χ b a hb ha) =
      -integralH2Class (k := ℤ) (cyclicParameterCarry χ a)
        (cyclicParameterCarry_isCocycle χ a ha) := by
  let c : continuousTwoCocycles (G := G) (M := M) :=
    ⟨cyclicParameterCarry χ a, cyclicParameterCarry_isCocycle χ a ha⟩
  change _ = -integralH2ClassHom c
  rw [← map_neg]
  apply (integralH2Class_eq_iff _ (-c).val
    (cyclicRootRatioCup_isCocycle χ b a hb ha) (-c).property).mpr
  refine ⟨cyclicRootLift χ b, fun g h => ?_⟩
  have he := cyclicRootLift_differential χ b g h
  rw [hb] at he
  change _ = cyclicRootRatioCup χ b (g, h) - -cyclicParameterCarry χ a (g, h)
  simpa only [sub_neg_eq_add] using he

end LocalClassFieldTheory
