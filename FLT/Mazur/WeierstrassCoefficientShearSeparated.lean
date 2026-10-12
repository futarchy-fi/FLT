/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearTorusDomain
public import FLT.Mazur.WeierstrassDividedGlobalFiniteProper

/-!
# Separatedness of the complete coefficient equation model

The actual gluing is proper over its coefficient ring. Its original torus action
preserves that structure, so dense comparisons can detect whole action morphisms.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type) [CommRing S] [Algebra R S] (r : S) (j : ℕ) (hj : j ≤ n)
local notation "g" => coefficientShearGluedStructure hπ data S r j hj
local notation "t" => Over.hom (MultiplicativeGroupScheme.gm S)

instance coefficientShearGluedStructure_isProper : IsProper g := by
  unfold coefficientShearGluedStructure
  infer_instance

instance coefficientShearGluedStructure_isSeparated : IsSeparated g := inferInstance

variable (a : Sˣ) (ha : (a : S) = (W.map (algebraMap R S)).a₁ + 2 * r)
  (hr : r ^ 2 + (W.map (algebraMap R S)).a₁ * r - (W.map (algebraMap R S)).a₂ = 0)
  (h3 : (W.map (algebraMap R S)).a₃ = 0)
  (h4 : (W.map (algebraMap R S)).a₄ = 0)
  (h6 : (W.map (algebraMap R S)).a₆ = 0)

/-- The full torus action retains its first input's coefficient structure. -/
@[reassoc] theorem coefficientShearTorusAction_structure :
    coefficientShearTorusAction hπ data S r j hj a ha hr h3 h4 h6 ≫ g =
      pullback.fst t g ≫ t := by
  rw [coefficientShearTorusAction, Category.assoc, coefficientShearAction_structure]
  change coefficientShearTorusDomainMap hπ data S r j hj a ha hr h3 h4 h6 ≫ _ = _
  rw [coefficientShearTorusDomainMap_parameter_assoc,
    WeierstrassIntegralChart.rootShearTorusSmoothIso_structure]

end FLT.Mazur.WeierstrassDividedDepth
