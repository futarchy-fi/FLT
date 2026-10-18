/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicTransitionCover
public import FLT.Mazur.CyclicCharacteristicUnmarkedRelation
public import FLT.Mazur.CyclicCharacteristicDisjointQuotient

/-!
# Scheme spans identifying the two characteristic charts in moduli

The transition sources are actual schemes covering the integer-invertible
open in each original normalized chart. Their two maps represent the same
full curve and subgroup. Composing with the constructed finite quotients
gives the cross-component spans that a further unmarked quotient must identify.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.CyclicCharacteristicAtlas
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup GroupSectionBaseChange
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] (b : Bool)

/-- The actual open where the opposite auxiliary characteristic is available. -/
def transitionOpen : (normalizedLocus n b).Opens :=
  CharacteristicTwoThree.unitOpen (normalizedLocus n b) (chartInteger (!b))

/-- The constructed fppf transition cover of that open. -/
def transitionCover : Scheme.Cover.{0} Scheme.fppfPrecoverage (transitionOpen n b).toScheme :=
  (exists_opposite_transition_on_open n b).choose

/-- The opposite-chart parameter on each actual transition source. -/
def transitionTarget (i : (transitionCover n b).I₀) :
    (transitionCover n b).X i ⟶ normalizedLocus n (!b) :=
  (exists_opposite_transition_on_open n b).choose_spec.choose i

/-- The original-chart parameter on the same actual transition source. -/
def transitionSource (i : (transitionCover n b).I₀) :
    (transitionCover n b).X i ⟶ normalizedLocus n b :=
  (transitionCover n b).f i ≫ (transitionOpen n b).ι

/-- Each transition source is flat over the original normalized chart. -/
instance transitionSource_flat (i : (transitionCover n b).I₀) :
    Flat (transitionSource n b i) := by
  let _ := ((transitionCover n b).map_prop i).1
  unfold transitionSource
  infer_instance

/-- Each transition source is locally of finite presentation over the original chart. -/
instance transitionSource_locallyOfFinitePresentation (i : (transitionCover n b).I₀) :
    LocallyOfFinitePresentation (transitionSource n b i) := by
  let _ := ((transitionCover n b).map_prop i).2
  unfold transitionSource
  infer_instance

/-- The two actual parameters compare the full subgroup and its chosen Cartier generator. -/
theorem transition_comparison (i : (transitionCover n b).I₀) :
    ∃ a : CompatibleIso ((normalizedSubgroup n (!b)).baseChange (transitionTarget n b i))
        ((normalizedSubgroup n b).baseChange (transitionSource n b i)),
      pullSection (transitionTarget n b i) (normalizedGenerator n (!b)) ≫ a.subgroup.hom =
        pullSection (transitionSource n b i) (normalizedGenerator n b) :=
  (exists_opposite_transition_on_open n b).choose_spec.choose_spec i

/-- These cross-characteristic scheme spans belong to the genuine unmarked relation. -/
theorem transition_unmarkedRelated (i : (transitionCover n b).I₀) :
    UnmarkedRelated n (!b) b (transitionTarget n b i) (transitionSource n b i) :=
  ⟨(transition_comparison n b i).choose⟩

/-- The transition sources cover precisely the opposite-characteristic open. -/
theorem transitionSource_covers (x : normalizedLocus n b) :
    (∃ i, x ∈ Set.range (transitionSource n b i)) ↔ x ∈ transitionOpen n b := by
  constructor
  · rintro ⟨i, y, rfl⟩
    exact ((transitionCover n b).f i y).2
  · intro hx
    let C : Scheme.Cover (Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation))
        (transitionOpen n b).toScheme := transitionCover n b
    obtain ⟨i, y, hy⟩ := C.exists_eq (⟨x, hx⟩ : (transitionOpen n b).toScheme)
    refine ⟨i, y, ?_⟩
    change (transitionOpen n b).ι ((transitionCover n b).f i y) = x
    rw [hy]
    rfl

/-- The source-side quotient parameter in the already constructed single quotient scheme. -/
def transitionQuotientSource (i : (transitionCover n b).I₀) :
    (transitionCover n b).X i ⟶ normalizedDisjointQuotient n :=
  transitionSource n b i ≫ normalizedQuotientMap n b ≫
    normalizedDisjointQuotientInclusion n b

/-- The opposite-side quotient parameter on the same scheme. -/
def transitionQuotientTarget (i : (transitionCover n b).I₀) :
    (transitionCover n b).X i ⟶ normalizedDisjointQuotient n :=
  transitionTarget n b i ≫ normalizedQuotientMap n (!b) ≫
    normalizedDisjointQuotientInclusion n (!b)

end FLT.Mazur.CyclicCharacteristicAtlas
