/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearActionDomain

/-!
# The original smooth action on the complete sheared equation model

Reconstruct the two inputs, use the independently constructed coefficient
action, and return through the proved gluing isomorphism. The resulting
whole morphism is cartesian over the original integral action.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [CommRing S] [Algebra R S] (r : S) (j : ℕ) (hj : j ≤ n)
local notation "V" => W.map (algebraMap R S)
local notation "f" => integralSmoothStructure V
local notation "g" => coefficientShearGluedStructure hπ data S r j hj
local notation "p" => coefficientShearGluedProjection hπ data S r j hj
local notation "E" => coefficientShearGluedIso hπ data S r j hj
local notation "D" => coefficientShearActionDomainMap hπ data S r j hj
local notation "A" => finiteGlobalCoefficientAction hπ data j hj S
local notation "P" => coefficientShearOriginalActionProduct hπ data S r j hj

/-- The actual original smooth action, on the complete sheared equation gluing. -/
def coefficientShearAction : coefficientShearActionDomain hπ data S r j hj ⟶
    coefficientShearGlued hπ data S r j hj := D ≫ A ≫ (E).inv

/-- The entire action agrees with the independent coefficient action after reconstruction. -/
@[reassoc] theorem coefficientShearAction_reconstruction :
    coefficientShearAction hπ data S r j hj ≫ (E).hom = D ≫ A := by
  rw [coefficientShearAction, Category.assoc, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

/-- The actual action has the coefficient map of its unchanged smooth input. -/
@[reassoc] theorem coefficientShearAction_structure :
    coefficientShearAction hπ data S r j hj ≫ g = pullback.fst f g ≫ f := by
  change coefficientShearAction hπ data S r j hj ≫
    (E).hom ≫ pullback.fst _ _ = _
  rw [coefficientShearAction_reconstruction_assoc, finiteGlobalCoefficientAction_structure,
    coefficientShearActionDomainMap_parameter_assoc]

/-- Projection retains the whole original integral action on both original inputs. -/
@[reassoc] theorem coefficientShearAction_projection :
    coefficientShearAction hπ data S r j hj ≫ p =
      P ≫ finiteGlobalAction hπ data j hj := by
  rw [coefficientShearGluedProjection, coefficientShearAction_reconstruction_assoc,
    finiteGlobalCoefficientAction_projection]
  rfl

/-- The complete sheared action square is cartesian over the original integral action. -/
theorem coefficientShearAction_isPullback :
    IsPullback P (coefficientShearAction hπ data S r j hj)
      (finiteGlobalAction hπ data j hj) p := by
  have H : IsPullback D (coefficientShearAction hπ data S r j hj) A (E).hom := by
    let _ : IsIso D := (coefficientShearActionDomainIso hπ data S r j hj).isIso_hom
    exact IsPullback.of_horiz_isIso
      ⟨(coefficientShearAction_reconstruction hπ data S r j hj).symm⟩
  exact H.paste_horiz (finiteGlobalCoefficientAction_isPullback hπ data j hj S)

/-- Both original projections determine a candidate action on the full domain uniquely. -/
theorem coefficientShearAction_unique
    (b : coefficientShearActionDomain hπ data S r j hj ⟶
      coefficientShearGlued hπ data S r j hj)
    (hb : b ≫ g = pullback.fst f g ≫ f)
    (hp : b ≫ p = P ≫ finiteGlobalAction hπ data j hj) :
    b = coefficientShearAction hπ data S r j hj := by
  apply (coefficientShearGlued_isPullback hπ data S r j hj).hom_ext
  · exact hb.trans (coefficientShearAction_structure hπ data S r j hj).symm
  · exact hp.trans (coefficientShearAction_projection hπ data S r j hj).symm

end FLT.Mazur.WeierstrassDividedDepth
