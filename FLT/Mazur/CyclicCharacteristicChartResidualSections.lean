/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicChartLocallyRinged
public import FLT.Mazur.CyclicCharacteristicLocallyRingedDescent

/-!
# Actual characteristic sections satisfy the full residual relation

The characteristic projection coequalizes the original same-chart comparison
scheme as locally ringed morphisms. Pullback therefore lands in the equalizer
of its two original maps on regular functions. Surjectivity of this section
comparison still requires reconstruction across the other characteristic.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.CyclicCharacteristicOrbit
open CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n]

/-- Every ordered chart comparison gives equality of the full locally ringed projections. -/
theorem chartLocallyRingedProjection_condition (b c : Bool) :
    (productArrowSource n b c).toLRSHom ≫ chartLocallyRingedProjection n b =
      (productArrowTarget n b c).toLRSHom ≫ chartLocallyRingedProjection n c := by
  have h := congrArg ((disjointComparisonInclusion n b c).toLRSHom ≫ ·)
    (invariantLocallyRingedProjection_condition n)
  simp only [← Category.assoc] at h
  change ((disjointComparisonInclusion n b c ≫
    disjointComparisonSource n).toLRSHom ≫ _) =
      ((disjointComparisonInclusion n b c ≫ disjointComparisonTarget n).toLRSHom ≫ _) at h
  rw [disjointComparisonInclusion_source, disjointComparisonInclusion_target] at h
  simpa only [chartLocallyRingedProjection, Scheme.Hom.comp_toLRSHom,
    Category.assoc] using h

/-- No same-chart residual arrows are lost by restricting to the characteristic orbit open. -/
theorem chartToInvariantOpen_condition (b : Bool) :
    (productArrowSource n b b).toLRSHom ≫ chartToInvariantOpen n b =
      (productArrowTarget n b b).toLRSHom ≫ chartToInvariantOpen n b := by
  rw [← cancel_mono ((invariantLocallyRingedSpace n).ofRestrict
    (integerOpen n (chartInteger b)).isOpenEmbedding)]
  simp only [Category.assoc, chartToInvariantOpen_comp]
  exact chartLocallyRingedProjection_condition n b b

/-- The residual invariant subring uses the actual full same-chart arrow scheme. -/
def chartResidualSections (b : Bool) : Subring Γ(normalizedLocus n b, ⊤) :=
  RingHom.eqLocus (productArrowSource n b b).appTop.hom
    (productArrowTarget n b b).appTop.hom

/-- Pullback of characteristic invariant sections along the actual locally ringed factor. -/
def chartInvariantSectionMap (b : Bool) :
    (invariantSheaf n).obj.obj (op (integerOpen n (chartInteger b))) ⟶
      Γ(normalizedLocus n b, ⊤) :=
  (invariantOpenSectionsIso n _).inv ≫
    LocallyRingedSpace.Γ.map (chartToInvariantOpen n b).op

/-- The two original same-chart section pullbacks agree on every invariant section. -/
theorem chartInvariantSectionMap_condition (b : Bool) :
    chartInvariantSectionMap n b ≫ (productArrowSource n b b).appTop =
      chartInvariantSectionMap n b ≫ (productArrowTarget n b b).appTop := by
  have h := congrArg (fun f => LocallyRingedSpace.Γ.map f.op)
    (chartToInvariantOpen_condition n b)
  change LocallyRingedSpace.Γ.map ((chartToInvariantOpen n b).op ≫
    (productArrowSource n b b).toLRSHom.op) =
      LocallyRingedSpace.Γ.map ((chartToInvariantOpen n b).op ≫
        (productArrowTarget n b b).toLRSHom.op) at h
  simp only [Functor.map_comp] at h
  exact congrArg ((invariantOpenSectionsIso n _).inv ≫ ·) h

/-- The characteristic section comparison lands in the genuine residual equalizer ring. -/
def chartResidualSectionMap (b : Bool) :
    (invariantSheaf n).obj.obj (op (integerOpen n (chartInteger b))) →+*
      chartResidualSections n b :=
  (chartInvariantSectionMap n b).hom.codRestrict _ (fun s => by
    change (productArrowSource n b b).appTop (chartInvariantSectionMap n b s) =
      (productArrowTarget n b b).appTop (chartInvariantSectionMap n b s)
    exact congrArg (fun f => f s) (chartInvariantSectionMap_condition n b))

/-- The residual comparison keeps the original section pullback. -/
theorem chartResidualSectionMap_val (b : Bool)
    (s : (invariantSheaf n).obj.obj (op (integerOpen n (chartInteger b)))) :
    (chartResidualSectionMap n b s).val = chartInvariantSectionMap n b s := rfl

end FLT.Mazur.CyclicCharacteristicOrbit
