/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicOddNormalizedGenerator
public import FLT.Mazur.OddWeierstrassPointedCubicHomNormalizedOriginalGenerator

/-!
# The actual odd normalized chart retains the original pointed cubic generator

Factor the auxiliary-cover parameter through the closed normalized subgroup
locus. The direct atlas subgroup is compared with the original cubic subgroup,
retaining the specified pulled Cartier generator throughout.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.OddWeierstrassParameter
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup
open CyclicCharacteristicAtlas GroupSectionBaseChange
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} (W : WeierstrassCurve Γ(S, ⊤)) [W.IsElliptic]
  (h₃ : IsUnit (3 : Γ(S, ⊤))) {n : ℕ} [NeZero n]
  (H : (pointedCubicFamily W).FiniteSubgroup n)
  {P : 𝟙_ (Over S) ⟶ H.carrier} (hP : H.IsCartierGenerator P)
local notation "φ" => H.generatorCurveMarking hP
local notation "k" => Over.hom (pointedCubicAuxiliaryCover W h₃)
local notation "f" => Over.Hom.left (pointedCubicHomAuxiliaryParameter W h₃ φ)
local notation "hf" => pointedCubicHomPrescribed_equation W h₃ H hP
local notation "q" => cyclicHomNormalizedLocusPoint n f hf

/-- The actual direct atlas subgroup retains the whole original cubic and finite subgroup. -/
def pointedCubicActualNormalizedIso :
    CompatibleIso ((normalizedSubgroup n true).baseChange q) (H.baseChange k) :=
  (oddNormalizedSourceIso n f hf).trans (pointedCubicHomNormalizedOriginalIso W h₃ H hP)

/-- Its universal generator is the prescribed original Cartier generator on the auxiliary cover. -/
theorem pointedCubicActualNormalizedIso_generator :
    pullSection q (oddNormalizedGenerator n) ≫
      (pointedCubicActualNormalizedIso W h₃ H hP).subgroup.hom = pullSection k P := by
  change _ ≫ ((oddNormalizedSourceIso n f hf).subgroup.hom ≫
    (pointedCubicHomNormalizedOriginalIso W h₃ H hP).subgroup.hom) = _
  rw [← Category.assoc, oddNormalizedSourceIso_generator]
  exact pointedCubicHomNormalizedOriginalIso_generator W h₃ H hP

end FLT.Mazur.OddWeierstrassParameter
