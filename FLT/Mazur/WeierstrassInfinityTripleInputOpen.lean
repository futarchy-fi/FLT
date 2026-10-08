/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityInputTriple
public import FLT.Mazur.WeierstrassInfinityTripleSections

/-!
# The full infinity member is open in the input chart triple

The four-law intersection factors through the actual three-input chart.
Its inclusion is open by cancellation against the open triple chart inclusion.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open FLT.Mazur.ProjectiveSpace

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (hΔ : IsUnit W.Δ)

/-- Lift the actual full member to the product of its three infinity input charts. -/
def infinityTripleFullInputChart : InfinityTripleFull W hΔ ⟶ InfinityInputTriple W :=
  pullback.lift (infinityTripleFullFirst W hΔ ≫ infinityAdditionInclusion W)
    (infinityTripleFullLast W hΔ ≫
      Spec.map (CommRingCat.ofHom (infinityInputRight W).toRingHom)) (by
      simp only [Category.assoc, infinityAdditionInclusion, chartStructure, specAlgHom_base]
      exact (infinityTripleFullLast_base W hΔ).symm)

/-- The lift preserves the original first pair. -/
@[reassoc (attr := simp)] theorem infinityTripleFullInputChart_pair :
    infinityTripleFullInputChart W hΔ ≫ infinityInputTriplePair W =
      infinityTripleFullFirst W hΔ ≫ infinityAdditionInclusion W :=
  pullback.lift_fst _ _ _

/-- The lift preserves the original third chart input. -/
@[reassoc (attr := simp)] theorem infinityTripleFullInputChart_third :
    infinityTripleFullInputChart W hΔ ≫ infinityInputTripleThird W =
      infinityTripleFullLast W hΔ ≫
        Spec.map (CommRingCat.ofHom (infinityInputRight W).toRingHom) :=
  pullback.lift_snd _ _ _

/-- The chart lift is the original inclusion into the global triple product. -/
theorem infinityTripleFullInputChart_inclusion :
    infinityTripleFullInputChart W hΔ ≫ infinityInputTripleInclusion W =
      infinityTripleFullMap W hΔ := by
  apply pullback.hom_ext
  · rw [Category.assoc, infinityInputTripleInclusion_pair, ← Category.assoc,
      infinityTripleFullInputChart_pair, Category.assoc]
    exact infinityTripleFullFirst_inputs W hΔ
  · rw [Category.assoc, infinityInputTripleInclusion_third, ← Category.assoc,
      infinityTripleFullInputChart_third, Category.assoc,
      ← infinityGlobalDomain_snd, ← Category.assoc, infinityTripleFullLast_inputs,
      Category.assoc, integralCurveTripleLastPair_snd]

/-- The genuine full member is open in the actual input chart triple. -/
instance infinityTripleFullInputChart_isOpenImmersion :
    IsOpenImmersion (infinityTripleFullInputChart W hΔ) := by
  have : IsOpenImmersion
      (infinityTripleFullInputChart W hΔ ≫ infinityInputTripleInclusion W) := by
    rw [infinityTripleFullInputChart_inclusion]
    infer_instance
  exact IsOpenImmersion.of_comp _ (infinityInputTripleInclusion W)

/-- The first chart projection is the original first-law left input. -/
theorem infinityTripleFullInputChart_first :
    infinityTripleFullInputChart W hΔ ≫ infinityInputTripleFirst W =
      infinityTripleFullFirst W hΔ ≫
        Spec.map (CommRingCat.ofHom (infinityInputLeft W).toRingHom) := by
  rw [infinityInputTripleFirst, ← Category.assoc, infinityTripleFullInputChart_pair,
    Category.assoc, infinityAdditionInclusion, ← Spec.map_comp]
  rfl

/-- The second chart projection is the original first-law right input. -/
theorem infinityTripleFullInputChart_second :
    infinityTripleFullInputChart W hΔ ≫ infinityInputTripleSecond W =
      infinityTripleFullFirst W hΔ ≫
        Spec.map (CommRingCat.ofHom (infinityInputRight W).toRingHom) := by
  rw [infinityInputTripleSecond, ← Category.assoc, infinityTripleFullInputChart_pair,
    Category.assoc, infinityAdditionInclusion, ← Spec.map_comp]
  rfl

end FLT.Mazur.WeierstrassIntegralChart
