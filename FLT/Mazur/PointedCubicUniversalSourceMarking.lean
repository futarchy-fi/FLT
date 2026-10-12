/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PointedCubicUniversalSourceGroup
public import FLT.Mazur.GeneralizedCurveCyclicMarkingBaseChange

/-!
# The universal source marking retains the original cubic cyclic sections

Compare the actual sections after projection to the universal group. The
coefficient and parameter equations identify all cyclic labels, including on
nonreduced test schemes, through the constructed source group isomorphism.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.GeneralizedEllipticCurve
open WeierstrassIntegralChart UniversalWeierstrass AuxiliaryLevel
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} (W : WeierstrassCurve Γ(S, ⊤)) [W.IsElliptic]
  (h₂ : IsUnit (2 : Γ(S, ⊤))) {n : ℕ} [NeZero n]
  (φ : Multiplicative (ZMod n) →* (𝟙_ (Over S) ⟶ (pointedCubicFamily W).group))
  (hφ : UniversallyDistinctSections.UniversallyDistinct (fun i : ZMod n ↦ φ (.ofAdd i)))
  (h : Nat.Coprime 4 n)
local notation "k" => Over.hom (pointedCubicAuxiliaryCover W h₂)
local notation "f" => Over.Hom.left (pointedCubicUniversalCyclicParameter W h₂ φ hφ h)

/-- The source comparison carries every original pulled cyclic section to its full source label. -/
theorem pointedCubicUniversalSourceGroupIso_cyclic (b : Multiplicative (ZMod n)) :
    pullCyclicMarking k φ b ≫
      (pointedCubicUniversalSourceGroupIso W h₂ φ hφ h).hom.hom.hom.hom =
        cyclicSchemeOriginalMarking n f (1, b) := by
  apply cyclicSchemeOriginalMarking_ext
  rw [Over.comp_left, Category.assoc, pointedCubicUniversalSourceGroupIso_fst,
    ← Category.assoc]
  change ((pullCyclicMarking k φ b).left ≫
    pullback.fst (pointedCubicFamily W).group.hom k) ≫ _ = _
  rw [pullCyclicMarking_fst, Category.assoc]
  simpa only [Over.comp_left] using
    (pointedCubicUniversalCyclicParameter_cyclic W h₂ φ hφ h b).symm

end FLT.Mazur.GeneralizedEllipticCurve
