/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassPointedCubicHomRetainedSubgroup
public import FLT.Mazur.OddWeierstrassCyclicHomPrescribedGeneratorComparison

/-!
# The actual odd normalized cubic cover retains its original generator

The reconstructed normalized source is compared with the original full cubic
and finite subgroup on the auxiliary cover. Its chosen universal label one
maps to the original pulled Cartier generator.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.OddWeierstrassParameter
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} (W : WeierstrassCurve Γ(S, ⊤)) [W.IsElliptic]
  (h₃ : IsUnit (3 : Γ(S, ⊤))) {n : ℕ} [NeZero n]
  (H : (pointedCubicFamily W).FiniteSubgroup n)
  {P : 𝟙_ (Over S) ⟶ H.carrier} (hP : H.IsCartierGenerator P)
local notation "φ" => H.generatorCurveMarking hP
local notation "k" => Over.hom (pointedCubicAuxiliaryCover W h₃)
local notation "f" => Over.Hom.left (pointedCubicHomAuxiliaryParameter W h₃ φ)
local notation "J" => pointedCubicHomRetainedSubgroup W h₃ φ H
local notation "hJ" => pointedCubicHomRetained_ideal W h₃ φ H hP rfl

/-- The parameter built from the original subgroup satisfies the actual multiplication equation. -/
theorem pointedCubicHomPrescribed_equation : cyclicHomMultiplicationEquation n f = 0 :=
  cyclicHomMultiplicationEquation_of_subgroup n f J hJ

local notation "hf" => pointedCubicHomPrescribed_equation W h₃ H hP
local notation "fN" => cyclicHomNormalizedPoint n f
local notation "hN" => cyclicHomNormalization_equation n f hf

/-- The normalized source retains the actual original full cubic subgroup on its auxiliary cover. -/
def pointedCubicHomNormalizedOriginalIso :
    CompatibleIso (cyclicHomSubgroup n fN hN) (H.baseChange k) :=
  (cyclicHomNormalizedPrescribedSubgroupIso n f hf J hJ).trans
    (pointedCubicHomRetainedIso W h₃ φ H).symm

/-- The chosen normalized label one is the original Cartier generator under the full comparison. -/
theorem pointedCubicHomNormalizedOriginalIso_generator :
    (cyclicHomSubgroup n fN hN).orbitGenerator (cyclicHomSourceMarking n fN)
      (cyclicHomSubgroup_ideal n fN hN) ≫
        (pointedCubicHomNormalizedOriginalIso W h₃ H hP).subgroup.hom =
      H.pullGenerator k P := by
  change _ ≫ ((cyclicHomNormalizedPrescribedSubgroupIso n f hf J hJ).subgroup.hom ≫
    (pointedCubicHomRetainedIso W h₃ φ H).subgroup.inv) = _
  rw [← Category.assoc, cyclicHomNormalizedPrescribedSubgroupIso_generator n f hf J hJ
    (pointedCubicHomRetained_generator W h₃ φ H hP)
    (pointedCubicHomRetained_marking W h₃ φ H hP rfl)]
  exact Category.comp_id _

end FLT.Mazur.OddWeierstrassParameter
