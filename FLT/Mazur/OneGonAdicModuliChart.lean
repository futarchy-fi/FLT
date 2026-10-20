/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonAdicBoundaryLevel
public import FLT.Mazur.CyclicCharacteristicNormalizedSubgroup

/-!
# The genuine adic chart and its smooth generic transition

The integral complete-base family defines a natural modular map on every test
scheme. Its original generic fiber admits the existing normalized smooth charts.
The base here is Z[[X]]; finite-presentation algebraization is not asserted.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.OneGonAdicModuliChart
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup
open OneGonAdicCharacterTower IntegralOneGonSpecializations
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n]

/-- The original integral complete coefficient scheme. -/
abbrev base : Scheme := Spec (.of (PowerSeries ℤ))

/-- The actual nonconstant integral family with its full ample cyclic subgroup. -/
def level : ampleCyclicLevels base n :=
  canonicalLevel (PolygonInfinitesimalStages.parameterIdeal ℤ) PowerSeries.X
    (Ideal.subset_span (Set.mem_singleton _)) n

/-- Every scheme test of the actual integral degeneration has its original modular class. -/
def moduliMap : yoneda.obj base ⋙ uliftFunctor.{1} ⟶ ampleCyclicClassPresheaf n where
  app _ := ↾(fun q ↦ ampleCyclicClassesPullback q.down n (integralCanonicalLevelClass n))
  naturality _ _ g := by
    ext q
    exact congrFun (ampleCyclicClassesPullback_comp q.down g.unop n)
      (integralCanonicalLevelClass n)

/-- Restricting the actual adic chart commutes with arbitrary scheme base change. -/
theorem moduliMap_pullback {T U : Scheme} (g : U ⟶ T) (q : T ⟶ base) :
    (moduliMap n).app (Opposite.op U) (ULift.up (g ≫ q)) =
      ampleCyclicClassesPullback g n ((moduliMap n).app (Opposite.op T) (ULift.up q)) :=
  congrFun (ampleCyclicClassesPullback_comp q g n) (integralCanonicalLevelClass n)

/-- The actual generic fiber is covered by the existing normalized smooth subgroup charts. -/
theorem generic_normalized_cover :
    ∃ (C : Scheme.Cover.{0} Scheme.fppfPrecoverage (Spec (.of GenericField)))
      (b : C.I₀ → Bool)
      (q : ∀ i, C.X i ⟶ CyclicCharacteristicAtlas.normalizedLocus n (b i)),
      ∀ i, (CyclicCharacteristicAtlas.normalizedModuliMap n (b i)).app
        (Opposite.op (C.X i)) (ULift.up (q i)) =
          (moduliMap n).app (Opposite.op (C.X i)) (ULift.up (C.f i ≫ genericMap)) := by
  let a := ampleCyclicLevelsPullback genericMap n (level n)
  let _ : Smooth a.val.1.curve.hom := generic_smooth_dimension.smooth
  obtain ⟨C, b, q, hq⟩ :=
    CyclicCharacteristicAtlas.exists_normalized_moduli_fppf_cover n a.val.2
      a.property.1 a.property.2
  refine ⟨C, b, q, fun i ↦ ?_⟩
  rw [moduliMap_pullback]
  exact hq i

end FLT.Mazur.OneGonAdicModuliChart
