/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SmoothSectionCartier
public import FLT.Mazur.SectionCartesianKernel
public import FLT.Mazur.RelativeCartierOriginalSquare

/-!
# The universal full point ideal on a smooth relative curve

The diagonal over the curve itself spreads a point condition. Specialization
retains the actual section kernel, including on nonreduced parameter schemes.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {X S : Scheme} (f : X ⟶ S)

/-- The point ideal with parameter space the original curve. -/
def universalPointIdeal : (pullback f f).IdealSheafData := (pullback.diagonal f).ker

/-- The universal point ideal is a relative Cartier ideal on a smooth separated curve. -/
theorem universalPointIdeal_relativeCartier [IsSeparated f]
    [SmoothOfRelativeDimension 1 f] :
    RelativeEffectiveCartier (pullback.snd f f) (universalPointIdeal f) := by
  let _ : SmoothOfRelativeDimension 1 (pullback.snd f f) :=
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) f f inferInstance
  exact smoothSectionCartier _ _ inferInstance inferInstance (pullback.diagonal_snd f)

variable {Y T : Scheme} {p : Y ⟶ X} {q : Y ⟶ T} {g : T ⟶ S}
  (H : IsPullback p q f g) (s : T ⟶ Y) (hs : s ≫ q = 𝟙 _)

/-- The original family maps to the universal pointed curve using its given section. -/
def pointConditionMap : Y ⟶ pullback f f :=
  pullback.lift p (q ≫ s ≫ p) (by simp only [Category.assoc, H.w, reassoc_of% hs])

@[reassoc (attr := simp)]
lemma pointConditionMap_fst : pointConditionMap f H s hs ≫ pullback.fst f f = p :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma pointConditionMap_snd :
    pointConditionMap f H s hs ≫ pullback.snd f f = q ≫ s ≫ p :=
  pullback.lift_snd _ _ _

include H hs in
/-- The parameter point retains its original map to the base. -/
lemma pointCondition_parameter_over : (s ≫ p) ≫ f = g := by
  rw [Category.assoc, H.w, reassoc_of% hs]

/-- The universal family specializes to the original family square. -/
theorem pointConditionMap_isPullback :
    IsPullback (pointConditionMap f H s hs) q (pullback.snd f f) (s ≫ p) := by
  apply IsPullback.of_right (h₁₂ := pullback.fst f f) (h₂₂ := f)
    (v₁₃ := f) ?_ (pointConditionMap_snd f H s hs) (IsPullback.of_hasPullback f f)
  simpa only [pointConditionMap_fst, pointCondition_parameter_over f H s hs] using H

/-- Specialization preserves the full section ideal, not merely its support. -/
theorem universalPointIdeal_comap [IsSeparated f] :
    (universalPointIdeal f).comap (pointConditionMap f H s hs) = s.ker := by
  apply section_ker_comap_of_cartesian (pointConditionMap_isPullback f H s hs)
    s (pullback.diagonal f) hs (pullback.diagonal_snd f)
  apply pullback.hom_ext <;> simp [reassoc_of% hs]

end FLT.Mazur.FCurve
