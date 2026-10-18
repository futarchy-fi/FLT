/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicEvenNormalizedGenerator
public import FLT.Mazur.PointedCubicHomNormalizedOriginalGenerator

/-!
# The actual normalized chart retains the original pointed cubic generator

Factor the auxiliary-cover parameter through the closed normalized subgroup
locus. The direct atlas subgroup is compared with the original cubic subgroup,
retaining the specified pulled Cartier generator throughout.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.GeneralizedEllipticCurve
open UniversalWeierstrass CyclicCharacteristicAtlas FiniteSubgroup GroupSectionBaseChange
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} (W : WeierstrassCurve Γ(S, ⊤)) [W.IsElliptic]
  (h₂ : IsUnit (2 : Γ(S, ⊤))) {n : ℕ} [NeZero n]
  (H : (pointedCubicFamily W).FiniteSubgroup n)
  {P : 𝟙_ (Over S) ⟶ H.carrier} (hP : H.IsCartierGenerator P)
local notation "φ" => H.generatorCurveMarking hP
local notation "k" => Over.hom (pointedCubicAuxiliaryCover W h₂)
local notation "f" => Over.Hom.left (pointedCubicHomAuxiliaryParameter W h₂ φ)
local notation "hf" => pointedCubicHomPrescribed_equation W h₂ H hP
local notation "q" => cyclicHomNormalizedLocusPoint n f hf

/-- The actual direct atlas subgroup retains the whole original cubic and finite subgroup. -/
def pointedCubicActualNormalizedIso :
    CompatibleIso ((normalizedSubgroup n false).baseChange q) (H.baseChange k) :=
  (evenNormalizedSourceIso n f hf).trans (pointedCubicHomNormalizedOriginalIso W h₂ H hP)

/-- Its universal generator is the prescribed original Cartier generator on the auxiliary cover. -/
theorem pointedCubicActualNormalizedIso_generator :
    pullSection q (evenNormalizedGenerator n) ≫
      (pointedCubicActualNormalizedIso W h₂ H hP).subgroup.hom = pullSection k P := by
  change _ ≫ ((evenNormalizedSourceIso n f hf).subgroup.hom ≫
    (pointedCubicHomNormalizedOriginalIso W h₂ H hP).subgroup.hom) = _
  rw [← Category.assoc, evenNormalizedSourceIso_generator]
  exact pointedCubicHomNormalizedOriginalIso_generator W h₂ H hP

end FLT.Mazur.GeneralizedEllipticCurve
