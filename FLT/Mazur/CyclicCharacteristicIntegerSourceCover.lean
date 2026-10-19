/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicOppositeLocallyRinged

/-!
# The two actual components of a characteristic source open

The selected normalized chart and the opposite transition open form an actual
open cover of the inverse image of the characteristic orbit open. These are
original scheme domains on which residual functions can be assembled.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicOrbit
open CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] (b : Bool)

/-- The original source domain above the selected characteristic orbit open. -/
def integerSourceOpen : (normalizedDisjointSource n).Opens :=
  (pullOpen n (integerOpen n (chartInteger (!b)))).val

/-- The entire selected chart lies in this original source domain. -/
def selectedToIntegerSource : normalizedLocus n (!b) ⟶ (integerSourceOpen n b).toScheme :=
  IsOpenImmersion.lift (integerSourceOpen n b).ι (normalizedDisjointInclusion n (!b)) (by
    rintro _ ⟨x, rfl⟩
    exact ⟨⟨normalizedDisjointInclusion n (!b) x,
      normalized_mem_integerOpen n (!b) x⟩, rfl⟩)

/-- The opposite chart contributes its actual integer-invertible overlap. -/
def oppositeToIntegerSource :
    (transitionOpen n b).toScheme ⟶ (integerSourceOpen n b).toScheme :=
  IsOpenImmersion.lift (integerSourceOpen n b).ι
    ((transitionOpen n b).ι ≫ normalizedDisjointInclusion n b) (by
      rintro _ ⟨x, rfl⟩
      refine ⟨⟨normalizedDisjointInclusion n b x.val, ?_⟩, rfl⟩
      exact (mem_integerOpen_iff n (chartInteger (!b)) b x.val).mpr x.property)

/-- The selected source lift retains the original disjoint inclusion. -/
@[reassoc] theorem selectedToIntegerSource_comp :
    selectedToIntegerSource n b ≫ (integerSourceOpen n b).ι =
      normalizedDisjointInclusion n (!b) := IsOpenImmersion.lift_fac _ _ _

/-- The opposite source lift retains both original open inclusions. -/
@[reassoc] theorem oppositeToIntegerSource_comp :
    oppositeToIntegerSource n b ≫ (integerSourceOpen n b).ι =
      (transitionOpen n b).ι ≫ normalizedDisjointInclusion n b :=
  IsOpenImmersion.lift_fac _ _ _

instance selectedToIntegerSource_isOpenImmersion :
    IsOpenImmersion (selectedToIntegerSource n b) := by
  unfold selectedToIntegerSource
  infer_instance

instance oppositeToIntegerSource_isOpenImmersion :
    IsOpenImmersion (oppositeToIntegerSource n b) := by
  unfold oppositeToIntegerSource
  infer_instance

/-- The two original component schemes, indexed without replacing either by an affine model. -/
def integerSourceChart : Bool → Scheme
  | false => normalizedLocus n (!b)
  | true => (transitionOpen n b).toScheme

/-- Their actual open immersions into the inverse-image source scheme. -/
def integerSourceChartMap : (c : Bool) → integerSourceChart n b c ⟶
    (integerSourceOpen n b).toScheme
  | false => selectedToIntegerSource n b
  | true => oppositeToIntegerSource n b

/-- Every original source point above the characteristic orbit open is in one of these charts. -/
theorem integerSourceChartMap_covers (x : (integerSourceOpen n b).toScheme) :
    ∃ c y, integerSourceChartMap n b c y = x := by
  obtain ⟨c, y, hy⟩ := normalizedDisjointSource_covers n x.val
  by_cases hc : c = b
  · subst c
    have hx := x.property
    change projection n x.val ∈ integerOpen n (chartInteger (!b)) at hx
    rw [← hy] at hx
    have hm := (mem_integerOpen_iff n (chartInteger (!b)) b y).mp hx
    refine ⟨true, ⟨y, hm⟩, ?_⟩
    apply Subtype.ext
    exact (congrArg (fun f => f ⟨y, hm⟩) (oppositeToIntegerSource_comp n b)).trans hy
  · have hc' : c = !b := by cases b <;> cases c <;> simp_all
    subst c
    refine ⟨false, y, ?_⟩
    apply Subtype.ext
    exact (congrArg (fun f => f y) (selectedToIntegerSource_comp n b)).trans hy

/-- The selected chart and opposite overlap give an actual open cover of the source domain. -/
def integerSourceCover : (integerSourceOpen n b).toScheme.OpenCover :=
  Scheme.Cover.mkOfCovers _ (integerSourceChart n b) (integerSourceChartMap n b)
    (integerSourceChartMap_covers n b) (by
      intro c
      cases c <;> dsimp only [integerSourceChartMap] <;> infer_instance)

end FLT.Mazur.CyclicCharacteristicOrbit
