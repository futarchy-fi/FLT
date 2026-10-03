/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.ContinuousInflationBoundary
public import FLT.LocalClassFieldTheory.ContinuousRestriction

/-!
# Injectivity of continuous H2 inflation

The cochain descent theorem applies to the actual homology map. Its
kernel-H1 and invariant-coefficient premises can be discharged by Galois theory.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open CategoryTheory HomologicalComplex groupCohomology GaloisRepresentation.Extensions

variable {G H M P : Type} [Group G] [Group H]
  [AddCommGroup M] [AddCommGroup P] [DistribMulAction H M] [DistribMulAction G P]
  [TopologicalSpace G] [TopologicalSpace H]
  [TopologicalSpace M] [DiscreteTopology M] [TopologicalSpace P]
  (f : G →* H) (hf : Continuous f)
  (φ : Rep.res f (Rep.of (Representation.ofDistribMulAction ℤ H M)) ⟶
    Rep.of (Representation.ofDistribMulAction ℤ G P))

/-- The explicit continuous cocycle obtained by group pullback and coefficient inclusion. -/
def continuousInflatedTwoCochain (c : C(H × H, M)) : C(G × G, P) :=
  ⟨fun z => φ.hom (c (f z.1, f z.2)), continuous_of_discreteTopology.comp
    (c.continuous.comp ((hf.comp continuous_fst).prodMk (hf.comp continuous_snd)))⟩

/-- Pullback preserves the two-cocycle equation. -/
theorem continuousInflatedTwoCochain_isCocycle (c : C(H × H, M)) (hc : IsCocycle₂ c) :
    IsCocycle₂ (continuousInflatedTwoCochain f hf φ c) := by
  intro g h j
  change φ.hom (c (f (g * h), f j)) + φ.hom (c (f g, f h)) =
    g • φ.hom (c (f h, f j)) + φ.hom (c (f g, f (h * j)))
  rw [map_mul, map_mul, ← map_add, hc, map_add]
  congr 1
  exact Rep.hom_comm_apply φ g _

variable [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
  [IsTopologicalGroup H] [CompactSpace H] [TotallyDisconnectedSpace H]
  [DiscreteTopology P] [ContinuousSMul G P] [ContinuousSMul H M]

/-- The categorical inflation map sends the explicit class to the inflated cocycle class. -/
theorem continuousInflationH2_class (c : C(H × H, M)) (hc : IsCocycle₂ c) :
    (homologyMap (continuousRestriction f hf φ) 2).hom (integralH2Class (k := ℤ) c hc) =
      integralH2Class (k := ℤ) (continuousInflatedTwoCochain f hf φ c)
        (continuousInflatedTwoCochain_isCocycle f hf φ c hc) := by
  unfold integralH2Class
  apply cochainHomologyClass_map

/-- Hilbert 90 on the kernel proves injectivity on actual continuous H2. -/
theorem continuousInflationH2_injective (hq : Topology.IsQuotientMap f)
    (hi : Function.Injective φ.hom)
    (hfix : ∀ p : P, (∀ n, f n = 1 → n • p = p) → ∃ m, φ.hom m = p)
    (hker : ∀ z : ContinuousCocycle f.ker P, ∃ a : P, ∀ n, z.val n = n • a - a) :
    Function.Injective (homologyMap (continuousRestriction f hf φ) 2).hom := by
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  obtain ⟨c, hc, rfl⟩ := integralH2Class_surjective x
  rw [continuousInflationH2_class] at hx
  obtain ⟨b, hb⟩ := (integralH2Class_eq_zero _ _).mp hx
  apply (integralH2Class_eq_zero _ _).mpr
  exact continuousInflation_boundary_descends f hq φ.hom.toLinearMap.toAddMonoidHom hi
    (fun g m => Rep.hom_comm_apply φ g m) hfix hker c hc b hb

end LocalClassFieldTheory
