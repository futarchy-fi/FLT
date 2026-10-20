/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonAdicModuliChart
public import FLT.Mazur.OneGonSmoothingPuncturedFamily

/-!
# Full smooth chart coverage of the actual punctured adic level

The constructed integral subgroup restricts to the original D(X) family.
Its entire punctured base has normalized ample cyclic charts, including in
characteristics two and three and for nonreduced tests of the puncture.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.OneGonAdicModuliChart
open GeneralizedEllipticCurve.FiniteSubgroup OneGonSmoothing
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n]

/-- The original integral adic level restricted to the full punctured complete base. -/
def puncturedLevel : ampleCyclicLevels (Spec (.of (PuncturedRing ℤ))) n :=
  ampleCyclicLevelsPullback (puncturedBaseInclusion ℤ) n (level n)

/-- The entire original adic pullback is smooth on D(X), not merely on its generic field. -/
theorem puncturedLevel_smooth_dimension :
    SmoothOfRelativeDimension 1 (puncturedLevel n).val.1.curve.hom := by
  let _ := puncturedFamily_smooth_dimension ℤ
  change SmoothOfRelativeDimension 1
    (pullback.snd (family (PowerSeries.X : PowerSeries ℤ)).hom (puncturedBaseInclusion ℤ))
  rw [← (puncturedComplete_isPullback ℤ).isoPullback_inv_snd]
  exact IsZariskiLocalAtSource.comp (P := @SmoothOfRelativeDimension 1)
    inferInstance (puncturedComplete_isPullback ℤ).isoPullback.inv

/-- Both characteristic charts cover the actual full subgroup on the entire punctured base. -/
theorem punctured_normalized_cover :
    ∃ (C : Scheme.Cover.{0} Scheme.fppfPrecoverage (Spec (.of (PuncturedRing ℤ))))
      (b : C.I₀ → Bool)
      (q : ∀ i, C.X i ⟶ CyclicCharacteristicAtlas.normalizedLocus n (b i)),
      ∀ i, (CyclicCharacteristicAtlas.normalizedModuliMap n (b i)).app
        (Opposite.op (C.X i)) (ULift.up (q i)) =
          (moduliMap n).app (Opposite.op (C.X i))
            (ULift.up (C.f i ≫ puncturedBaseInclusion ℤ)) := by
  let a := puncturedLevel n
  let _ : Smooth a.val.1.curve.hom := (puncturedLevel_smooth_dimension n).smooth
  obtain ⟨C, b, q, hq⟩ :=
    CyclicCharacteristicAtlas.exists_normalized_moduli_fppf_cover n a.val.2
      a.property.1 a.property.2
  refine ⟨C, b, q, fun i ↦ ?_⟩
  rw [moduliMap_pullback]
  exact hq i

/-- Arbitrary tests of the punctured family retain its smooth whole curve. -/
theorem puncturedLevel_test_smooth {T : Scheme} (g : T ⟶ Spec (.of (PuncturedRing ℤ))) :
    Smooth (((puncturedLevel n).val.1).baseChange g).curve.hom := by
  let _ := (puncturedLevel_smooth_dimension n).smooth
  exact inferInstanceAs (Smooth (pullback.snd (puncturedLevel n).val.1.curve.hom g))

end FLT.Mazur.OneGonAdicModuliChart
