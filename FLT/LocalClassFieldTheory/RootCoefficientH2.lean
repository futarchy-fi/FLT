/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.RootCoefficientBoundary
public import FLT.LocalClassFieldTheory.IntegralDegreeTwoComparison
public import FLT.LocalClassFieldTheory.ContinuousColimitNaturality

/-!
# Injectivity of root inclusion on actual continuous H²

The map is induced by the actual coefficient inclusion. Reflection of
continuous boundaries proves its injectivity on the cohomology complex.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open CategoryTheory KummerTheory groupCohomology

variable (K C : Type) [Field K] [Field C] [Algebra K C] [IsGalois K C]
  [TopologicalSpace (Additive Cˣ)] [DiscreteTopology (Additive Cˣ)]
  (n : ℕ) [NeZero n]

attribute [local instance] fieldUnitAction

/-- The natural root action is continuous for the discrete coefficient topology. -/
local instance rootCoefficientContinuous : ContinuousSMul Gal(C/K) (RootModule C n) := by
  constructor
  rw [continuous_prod_of_discrete_right]
  exact continuous_root_orbit (K := K)

/-- Actual root inclusion as a morphism of integral Galois representations. -/
def rootCoefficientMorphism :
    Rep.of (Representation.ofDistribMulAction ℤ Gal(C/K) (RootModule C n)) ⟶
      Rep.of (Representation.ofDistribMulAction ℤ Gal(C/K) (Additive Cˣ)) :=
  Rep.ofHom ⟨(rootCoefficientInclusion C n).toIntLinearMap, fun g => by
    apply LinearMap.ext
    intro x
    exact rootCoefficientInclusion_smul K C n g x⟩

omit [IsGalois K C] [DiscreteTopology (Additive Cˣ)] [NeZero n] in
/-- Coefficient inclusion preserves the explicit two-cocycle equation. -/
theorem includedRootTwoCochain_isCocycle
    (c : C(Gal(C/K) × Gal(C/K), RootModule C n)) (hc : IsCocycle₂ c) :
    IsCocycle₂ (includedRootTwoCochain K C n c) := by
  intro g h j
  change rootCoefficientInclusion C n (c (g * h, j)) +
    rootCoefficientInclusion C n (c (g, h)) =
      g • rootCoefficientInclusion C n (c (h, j)) +
        rootCoefficientInclusion C n (c (g, h * j))
  simpa only [map_add, rootCoefficientInclusion_smul] using
    congrArg (rootCoefficientInclusion C n) (hc g h j)

/-- Root inclusion induces this additive map on the actual continuous H² groups. -/
def rootCoefficientH2 : continuousCohomology ℤ Gal(C/K) (RootModule C n) 2 →+
    continuousCohomology ℤ Gal(C/K) (Additive Cˣ) 2 :=
  (continuousCoefficientCohomologyMap (rootCoefficientMorphism K C n) 2).hom.toAddMonoidHom

omit [NeZero n] in
/-- The categorical map includes an explicit cocycle pointwise. -/
theorem rootCoefficientH2_class
    (c : C(Gal(C/K) × Gal(C/K), RootModule C n)) (hc : IsCocycle₂ c) :
    rootCoefficientH2 K C n (integralH2Class (k := ℤ) c hc) =
      integralH2Class (k := ℤ) (includedRootTwoCochain K C n c)
        (includedRootTwoCochain_isCocycle K C n c hc) := by
  unfold rootCoefficientH2 continuousCoefficientCohomologyMap integralH2Class
  apply cochainHomologyClass_map

/-- Hilbert 90 and root correction prove actual H² coefficient-inclusion injectivity. -/
theorem rootCoefficientH2_injective [IsAlgClosed C] :
    Function.Injective (rootCoefficientH2 K C n) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  obtain ⟨c, hc, rfl⟩ := integralH2Class_surjective x
  rw [rootCoefficientH2_class] at hx
  apply (integralH2Class_eq_zero c hc).mpr
  exact (includedRootTwoCochain_coboundary_iff K C n c).mp
    ((integralH2Class_eq_zero _ _).mp hx)

end LocalClassFieldTheory
