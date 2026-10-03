/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.IntegralTwoClassEquality

/-!
# Additivity of explicit continuous H2 classes

Cocycle addition, subtraction, and natural multiples agree with the operations
in the homology of the continuous cochain complex.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open CategoryTheory groupCohomology

/-- Addition of cycles agrees with addition in categorical homology. -/
theorem cochainHomologyClass_add {k : Type} [CommRing k]
    (K : CochainComplex (ModuleCat k) ℕ) (n : ℕ) (c d : K.X n)
    (hc : (K.d n ((ComplexShape.up ℕ).next n)).hom c = 0)
    (hd : (K.d n ((ComplexShape.up ℕ).next n)).hom d = 0)
    (hcd : (K.d n ((ComplexShape.up ℕ).next n)).hom (c + d) = 0) :
    cochainHomologyClass K n (c + d) hcd =
      cochainHomologyClass K n c hc + cochainHomologyClass K n d hd := by
  unfold cochainHomologyClass
  rw [← map_add]
  apply congrArg (K.homologyπ n).hom
  apply (ModuleCat.mono_iff_injective (K.iCycles n)).mp inferInstance
  simp only [map_add, cochainCyclesMk_val]

variable {G M : Type} [Group G] [AddCommGroup M] [DistribMulAction G M]
  [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul G M]

/-- Continuous two-cocycles form an additive subgroup of continuous cochains. -/
abbrev continuousTwoCocycles : AddSubgroup C(G × G, M) where
  carrier := {c | IsCocycle₂ c}
  zero_mem' := by intro g h j; simp
  add_mem' := by
    intro c d hc hd g h j
    change (c (g * h, j) + d (g * h, j)) + (c (g, h) + d (g, h)) =
      g • (c (h, j) + d (h, j)) + (c (g, h * j) + d (g, h * j))
    rw [smul_add]
    calc
      _ = (c (g * h, j) + c (g, h)) + (d (g * h, j) + d (g, h)) := by abel
      _ = _ := by rw [hc, hd]; abel
  neg_mem' := by
    intro c hc g h j
    change -c (g * h, j) + -c (g, h) = g • -c (h, j) + -c (g, h * j)
    rw [smul_neg, ← neg_add, ← neg_add, hc]

/-- The map from explicit cocycles to actual H2 is additive. -/
def integralH2ClassHom : continuousTwoCocycles (G := G) (M := M) →+
    continuousCohomology ℤ G M 2 where
  toFun c := integralH2Class c.val c.property
  map_zero' := (integralH2Class_eq_zero _ _).mpr ⟨0, by intro g h; simp⟩
  map_add' c d :=
    cochainHomologyClass_add (continuousCochains ℤ G M) 2
      (continuousTwoCochain c.val) (continuousTwoCochain d.val) _ _ _

/-- Every H2 class is represented by an element of the cocycle subgroup. -/
theorem integralH2ClassHom_surjective :
    Function.Surjective (integralH2ClassHom (G := G) (M := M)) := by
  intro x
  obtain ⟨c, hc, h⟩ := integralH2Class_surjective x
  exact ⟨⟨c, hc⟩, h⟩

end LocalClassFieldTheory
