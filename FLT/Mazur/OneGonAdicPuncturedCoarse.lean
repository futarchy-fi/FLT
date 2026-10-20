/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonAdicPuncturedModuli
public import FLT.Mazur.SmoothCyclicCoarseMorphism

/-!
# The actual coarse morphism on the punctured integral adic level

The entire D(X) family has a morphism to the existing normalized coarse scheme.
Its normalized chart equations retain the full original adic subgroup, and
every further test restricts this same morphism. Extension across the boundary
is not asserted: that requires the enlarged coarse model.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.OneGonAdicModuliChart
open GeneralizedEllipticCurve.FiniteSubgroup OneGonSmoothing
open CyclicCharacteristicAtlas CyclicCharacteristicOrbit
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n]

/-- The actual morphism from the entire punctured integral base to the normalized coarse scheme. -/
def puncturedCoarseMorphism : Spec (.of (PuncturedRing ℤ)) ⟶ invariantOrbitScheme n := by
  let _ := (puncturedLevel_smooth_dimension n).smooth
  exact smoothCoarseMorphism n (puncturedLevel n).val.2
    (puncturedLevel n).property.1 (puncturedLevel n).property.2

/-- Every test restricts the same actual coarse morphism of the original punctured family. -/
theorem puncturedCoarseMorphism_test {T : Scheme} (g : T ⟶ Spec (.of (PuncturedRing ℤ))) :
    let a := ampleCyclicLevelsPullback g n (puncturedLevel n)
    let _ : Smooth a.val.1.curve.hom := puncturedLevel_test_smooth n g
    smoothCoarseMorphism n a.val.2 a.property.1 a.property.2 = g ≫ puncturedCoarseMorphism n := by
  let _ := (puncturedLevel_smooth_dimension n).smooth
  let _ := puncturedLevel_test_smooth n g
  exact smoothCoarseMorphism_pullback n (puncturedLevel n).val.2
    (puncturedLevel n).property.1 (puncturedLevel n).property.2 g

/-- Any original normalized representative of a punctured test has the prescribed coarse value. -/
theorem puncturedCoarseMorphism_chart {T : Scheme} (g : T ⟶ Spec (.of (PuncturedRing ℤ)))
    (b : Bool) (q : T ⟶ normalizedLocus n b)
    (hq : (normalizedModuliMap n b).app (Opposite.op T) (ULift.up q) =
      (moduliMap n).app (Opposite.op T) (ULift.up (g ≫ puncturedBaseInclusion ℤ))) :
    g ≫ puncturedCoarseMorphism n = q ≫ normalizedCoarseChart n b := by
  let a := ampleCyclicLevelsPullback g n (puncturedLevel n)
  let _ : Smooth a.val.1.curve.hom := puncturedLevel_test_smooth n g
  have ha : (normalizedModuliMap n b).app (Opposite.op T) (ULift.up q) =
      Quotient.mk _ a := by
    rw [moduliMap_pullback] at hq
    exact hq
  exact (puncturedCoarseMorphism_test n g).symm.trans
    (smoothCoarseMorphism_parameter n a.val.2 a.property.1 a.property.2 b q ha)

/-- The original D(X) cover satisfies the coarse chart equations on every covering member. -/
theorem puncturedCoarseMorphism_cover :
    ∃ (C : Scheme.Cover.{0} Scheme.fppfPrecoverage (Spec (.of (PuncturedRing ℤ))))
      (b : C.I₀ → Bool) (q : ∀ i, C.X i ⟶ normalizedLocus n (b i)),
      ∀ i, C.f i ≫ puncturedCoarseMorphism n = q i ≫ normalizedCoarseChart n (b i) := by
  obtain ⟨C, b, q, hq⟩ := punctured_normalized_cover n
  exact ⟨C, b, q, fun i ↦ puncturedCoarseMorphism_chart n (C.f i) (b i) (q i) (hq i)⟩

end FLT.Mazur.OneGonAdicModuliChart
