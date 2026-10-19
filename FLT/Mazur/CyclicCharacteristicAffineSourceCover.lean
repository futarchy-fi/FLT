/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicAffineOppositeCover

/-!
# Original source domains over the affine quotient refinement

The original selected affine chart and the exact opposite-chart open cover the
inverse image of the affine orbit domain. Both are actual open immersions into
the original source; no scheme structure on the quotient is presumed.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicOrbit
open CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] (b : Bool) (j : (invariantAffineCover n (!b)).I₀)
local notation "i" => (Sigma.mk (!b) j : InvariantAffineIndex n)

/-- The full original source domain above the selected affine orbit open. -/
def affineSourceOpen : (normalizedDisjointSource n).Opens :=
  (pullOpen n (affineOrbitOpen n i)).val

/-- The original selected affine chart maps into the source domain. -/
def selectedToAffineSource : invariantAffineChart n i ⟶ (affineSourceOpen n b j).toScheme :=
  IsOpenImmersion.lift (affineSourceOpen n b j).ι
    (invariantAffineInclusion n i ≫ normalizedDisjointInclusion n (!b)) (by
      rintro _ ⟨x, rfl⟩
      refine ⟨⟨normalizedDisjointInclusion n (!b) (invariantAffineInclusion n i x), ?_⟩, rfl⟩
      exact (affineOrbitProjection n i x).property)

/-- The exact opposite-chart open maps into the same original source domain. -/
def oppositeToAffineSource :
    (affineOppositeOpen n b j).toScheme ⟶ (affineSourceOpen n b j).toScheme :=
  IsOpenImmersion.lift (affineSourceOpen n b j).ι
    ((affineOppositeOpen n b j).ι ≫ normalizedDisjointInclusion n b) (by
      rintro _ ⟨x, rfl⟩
      exact ⟨⟨normalizedDisjointInclusion n b x.val, x.property⟩, rfl⟩)

/-- The selected source map retains both original inclusions. -/
@[reassoc] theorem selectedToAffineSource_comp :
    selectedToAffineSource n b j ≫ (affineSourceOpen n b j).ι =
      invariantAffineInclusion n i ≫ normalizedDisjointInclusion n (!b) :=
  IsOpenImmersion.lift_fac _ _ _

/-- The opposite source map retains both original inclusions. -/
@[reassoc] theorem oppositeToAffineSource_comp :
    oppositeToAffineSource n b j ≫ (affineSourceOpen n b j).ι =
      (affineOppositeOpen n b j).ι ≫ normalizedDisjointInclusion n b :=
  IsOpenImmersion.lift_fac _ _ _

instance selectedToAffineSource_isOpenImmersion :
    IsOpenImmersion (selectedToAffineSource n b j) := by
  unfold selectedToAffineSource
  infer_instance

instance oppositeToAffineSource_isOpenImmersion :
    IsOpenImmersion (oppositeToAffineSource n b j) := by
  unfold oppositeToAffineSource
  infer_instance

/-- The two actual component schemes of the refined source domain. -/
def affineSourceChart : Bool → Scheme
  | false => invariantAffineChart n i
  | true => (affineOppositeOpen n b j).toScheme

/-- Their actual open immersions into the source domain. -/
def affineSourceChartMap : (c : Bool) → affineSourceChart n b j c ⟶
    (affineSourceOpen n b j).toScheme
  | false => selectedToAffineSource n b j
  | true => oppositeToAffineSource n b j

/-- These two original charts cover the entire refined source domain. -/
theorem affineSourceChartMap_covers (x : (affineSourceOpen n b j).toScheme) :
    ∃ c y, affineSourceChartMap n b j c y = x := by
  obtain ⟨c, y, hy⟩ := normalizedDisjointSource_covers n x.val
  have hx := x.property
  change projection n x.val ∈ affineOrbitOpen n i at hx
  rw [← hy] at hx
  by_cases hc : c = b
  · subst c
    refine ⟨true, ⟨y, hx⟩, ?_⟩
    apply Subtype.ext
    exact (congrArg (fun f => f ⟨y, hx⟩) (oppositeToAffineSource_comp n b j)).trans hy
  · have hc' : c = !b := by cases b <;> cases c <;> simp_all
    subst c
    have hm : y ∈ Set.range (invariantAffineInclusion n i) :=
      Set.ext_iff.mp (affineOrbitOpen_preimage n i) y |>.mp hx
    obtain ⟨a, ha⟩ := hm
    refine ⟨false, a, ?_⟩
    apply Subtype.ext
    have he := congrArg (fun f => f a) (selectedToAffineSource_comp n b j)
    exact he.trans ((congrArg (normalizedDisjointInclusion n (!b)) ha).trans hy)

/-- The two component open immersions form a cover of the actual original source domain. -/
def affineSourceCover : (affineSourceOpen n b j).toScheme.OpenCover :=
  Scheme.Cover.mkOfCovers _ (affineSourceChart n b j) (affineSourceChartMap n b j)
    (affineSourceChartMap_covers n b j) (by
      intro c
      cases c <;> dsimp only [affineSourceChart, affineSourceChartMap] <;> infer_instance)

end FLT.Mazur.CyclicCharacteristicOrbit
