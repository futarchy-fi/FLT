/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicOrbitComparisons
public import FLT.Mazur.CyclicCharacteristicOrbitTopology
public import FLT.Mazur.CyclicCharacteristicQuotientTransitionSpan

/-!
# The residual orbit projection on the finite characteristic quotients

Each existing finite quotient maps continuously to the full comparison orbit
space. The actual transition spans agree there. This factors the topological
quotient without discarding the remaining comparison relation.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicOrbit
open CyclicCharacteristicAtlas
variable (n : ℕ) [NeZero n] (b : Bool)

/-- A point of the finite quotient is sent to the full orbit of any representative. -/
def finiteProjection (y : normalizedQuotient n b) : Orbit n :=
  projection n (normalizedDisjointInclusion n b
    ((normalizedQuotientMap n b).surjective y).choose)

/-- The residual projection recovers the original full orbit of every normalized point. -/
theorem finiteProjection_apply (x : normalizedLocus n b) :
    finiteProjection n b (normalizedQuotientMap n b x) =
      projection n (normalizedDisjointInclusion n b x) :=
  projection_eq_of_finite_quotient_eq n b _ x
    ((normalizedQuotientMap n b).surjective (normalizedQuotientMap n b x)).choose_spec

/-- The residual projection is continuous for the existing finite quotient topology. -/
theorem finiteProjection_continuous : Continuous (finiteProjection n b) := by
  apply (normalizedQuotientMap_isQuotientMap n b).continuous_iff.mpr
  have he : finiteProjection n b ∘ normalizedQuotientMap n b =
      projection n ∘ normalizedDisjointInclusion n b := funext (finiteProjection_apply n b)
  rw [he]
  exact (projection_continuous n).comp (normalizedDisjointInclusion n b).continuous

/-- The residual projection is a genuine continuous map on each finite quotient. -/
def finiteQuotientMap : (normalizedQuotient n b).toTopCat ⟶ space n :=
  TopCat.ofHom ⟨finiteProjection n b, finiteProjection_continuous n b⟩

/-- Its composite with the original finite quotient map is the original orbit map. -/
theorem normalizedQuotientMap_finiteQuotientMap :
    (normalizedQuotientMap n b).base ≫ finiteQuotientMap n b =
      (normalizedDisjointInclusion n b).base ≫ quotientMap n := by
  ext x
  exact finiteProjection_apply n b x

/-- Each actual transition span has identical images in the full orbit space. -/
theorem finiteProjection_transition (i : (transitionCover n b).I₀)
    (x : (transitionCover n b).X i) :
    finiteProjection n (!b) (normalizedQuotientMap n (!b) (transitionTarget n b i x)) =
      finiteProjection n b (normalizedQuotientMap n b (transitionSource n b i x)) := by
  rw [finiteProjection_apply, finiteProjection_apply]
  exact (projection_eq_iff n _ _).mpr
    (related_of_unmarked n (transition_unmarkedRelated n b i) x)

/-- Both arms on the actual quotient overlap opens agree after the residual projection. -/
theorem finiteQuotientMap_transition (i : (transitionCover n b).I₀) :
    (quotientTransitionTarget n b i).base ≫ (quotientTransitionOpen n (!b)).ι.base ≫
        finiteQuotientMap n (!b) =
      (quotientTransitionSource n b i).base ≫ (quotientTransitionOpen n b).ι.base ≫
        finiteQuotientMap n b := by
  ext x
  have ht := congrArg (fun k ↦ k x) (quotientTransitionTarget_inclusion n b i)
  have hs := congrArg (fun k ↦ k x) (quotientTransitionSource_inclusion n b i)
  simp only [Scheme.Hom.comp_apply] at ht hs
  change finiteProjection n (!b) ((quotientTransitionOpen n (!b)).ι
      (quotientTransitionTarget n b i x)) =
    finiteProjection n b ((quotientTransitionOpen n b).ι (quotientTransitionSource n b i x))
  rw [ht, hs]
  exact finiteProjection_transition n b i x

end FLT.Mazur.CyclicCharacteristicOrbit
