/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicFixedCover

/-!
# Actual transitions between the two normalized characteristic charts

Over the open domain of another characteristic chart, an arbitrary normalized
parameter has fppf local parameters in that chart. The comparisons retain the
entire curve, the full subgroup scheme and the specified Cartier generator.
These are moduli comparisons, not intersections in the disjoint source union.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.CyclicCharacteristicAtlas
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup GroupSectionBaseChange
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n]

/-- Both original characteristic families are smooth curves. -/
instance curve_smooth (b : Bool) : Smooth (curve n b).curve.hom := by
  cases b
  · change Smooth (UniversalWeierstrass.cyclicHomSourceCurve n
      (UniversalWeierstrass.cyclicHomUniversalMultiplicationLocusInclusion n)).curve.hom
    exact SmoothOfRelativeDimension.smooth 1 _
  · change Smooth (OddWeierstrassParameter.cyclicHomSourceCurve n
      (OddWeierstrassParameter.cyclicHomUniversalMultiplicationLocusInclusion n)).curve.hom
    exact SmoothOfRelativeDimension.smooth 1 _

/-- The actual normalized family remains smooth over its parameter scheme. -/
instance normalizedCurve_smooth (b : Bool) : Smooth (normalizedCurve n b).curve.hom :=
  inferInstanceAs (Smooth (pullback.snd (curve n b).curve.hom (normalizedInclusion n b)))

/-- Every test of a normalized family is a smooth curve. -/
instance normalizedCurve_baseChange_smooth (b : Bool) {T : Scheme}
    (q : T ⟶ normalizedLocus n b) : Smooth ((normalizedCurve n b).baseChange q).curve.hom :=
  inferInstanceAs (Smooth (pullback.snd (normalizedCurve n b).curve.hom q))

/-- Actual chart transitions locally preserve the full subgroup and its chosen generator. -/
theorem exists_normalized_transition_fppf_cover {T : Scheme} (b c : Bool)
    (q : T ⟶ normalizedLocus n b) (hc : IsUnit (chartInteger c : Γ(T, ⊤))) :
    ∃ (C : Scheme.Cover.{0} Scheme.fppfPrecoverage T)
      (r : ∀ i : C.I₀, C.X i ⟶ normalizedLocus n c),
      ∀ i, ∃ a : CompatibleIso ((normalizedSubgroup n c).baseChange (r i))
          ((normalizedSubgroup n b).baseChange (C.f i ≫ q)),
        pullSection (r i) (normalizedGenerator n c) ≫ a.subgroup.hom =
          pullSection (C.f i ≫ q) (normalizedGenerator n b) := by
  obtain ⟨C, r, hr⟩ := exists_fixed_characteristic_fppf_cover
    ((normalizedSubgroup n b).baseChange q) (normalizedGenerator_pull_cartier n b q) c hc
  refine ⟨C, r, fun i ↦ ?_⟩
  obtain ⟨a, ha⟩ := hr i
  refine ⟨a.trans (compatibleBaseChangeComp (normalizedSubgroup n b) q (C.f i)).symm, ?_⟩
  change pullSection (r i) (normalizedGenerator n c) ≫
    (a.subgroup.hom ≫ (compatibleBaseChangeComp _ q (C.f i)).subgroup.inv) = _
  rw [← Category.assoc, ha]
  exact compatibleBaseChangeComp_inv_section _ q (C.f i) (normalizedGenerator n b)

/-- The opposite characteristic is available over its actual integer-invertible open. -/
theorem exists_opposite_transition_on_open (b : Bool) :
    let B := CharacteristicTwoThree.unitOpen (normalizedLocus n b) (chartInteger (!b))
    ∃ (C : Scheme.Cover.{0} Scheme.fppfPrecoverage B.toScheme)
      (r : ∀ i : C.I₀, C.X i ⟶ normalizedLocus n (!b)),
      ∀ i, ∃ a : CompatibleIso ((normalizedSubgroup n (!b)).baseChange (r i))
          ((normalizedSubgroup n b).baseChange (C.f i ≫ B.ι)),
        pullSection (r i) (normalizedGenerator n (!b)) ≫ a.subgroup.hom =
          pullSection (C.f i ≫ B.ι) (normalizedGenerator n b) :=
  exists_normalized_transition_fppf_cover n b (!b) _
    (CharacteristicTwoThree.unitOpen_isUnit _ _)

end FLT.Mazur.CyclicCharacteristicAtlas
