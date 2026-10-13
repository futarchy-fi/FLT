/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearResidueAdjacent
public import FLT.Mazur.WeierstrassCoefficientShearResidueZeroExteriorEndpoints
public import FLT.Mazur.WeierstrassCoefficientShearScaleOneEndpoints
import all FLT.Mazur.WeierstrassCoefficientShearResidueAdjacent
import all FLT.Mazur.WeierstrassCoefficientShearResidueZeroExteriorEndpoints
import all FLT.Mazur.WeierstrassCoefficientShearScaleOneComponents
import all FLT.Mazur.WeierstrassCoefficientShearRetainedFiber
import all FLT.Mazur.WeierstrassCoefficientShearRetainedScaleOneConic

/-!
# The original start-zero exterior joins both first adjacent components

Both original conic origins coincide in the actual final target. The full
components and the complete exterior keep their independently built parameters.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
section Stage
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (j k : ℕ) (hj : j ≤ n) (hk : k ≤ n) (hstage : j = k)
  {depth : ℕ} (d : Data W π depth) (hd : 0 < depth) (hp : residue R π = 0)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))
local notation "r" => AdjoinRoot.root (nodeTangentPolynomial (W.map (residue R)))
variable [Fact (Irreducible (nodeTangentPolynomial (W.map (residue R))))]
  (a : (AdjoinRoot (nodeTangentPolynomial (W.map (residue R))))ˣ)

/-- Reindexing preserves the whole original ordered exterior lift. -/
@[reassoc] theorem coefficientShearResidueExteriorLift_stageIso :
    coefficientShearResidueExteriorLift hπ data j hj d hd hp a ≫
        (coefficientShearStageIso hπ data Q r j k hj hk hstage).hom =
      coefficientShearResidueExteriorLift hπ data k hk d hd hp a := by
  subst k
  exact Category.comp_id _
end Stage

variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0)
  (hm : maximalIdeal R = Ideal.span {π}) {n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (s : ℕ) (hs : s + 1 ≤ n) (hk : 2 * (0 + (s + 1)) ≤ depth)
  (h3 : W.a₃ ∈ maximalIdeal R ^ (depth + 1))
  (h4 : W.a₄ ∈ maximalIdeal R ^ (depth + 1))
  (hc : IsUnit W.c₄) (hspos : 0 < s)
local notation "V" => W.map (residue R)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial V)
local notation "r" => AdjoinRoot.root (nodeTangentPolynomial V)
variable [Fact (Irreducible (nodeTangentPolynomial (W.map (residue R))))]
local notation "j" => (⟨0, hspos⟩ : Fin s)
local notation "d" => data ⟨1, by omega⟩
local notation "lin" => nodalDepth_tangent_linear_zero hπ hm d (by dsimp; omega) h3 h4
local notation "a" => residueTangentComponentUnit W h3 h4 hc
local notation "ha" => residueTangentComponentUnit_val W h3 h4 hc
local notation "hr" => residueTangentEquation_root W
local notation "hp" => residueTangentEquation_zero W π
  (hm ▸ Ideal.mem_span_singleton_self π)
local notation "hres" => nodalDepth_residue_uniformizer hm
local notation "F" => coefficientShearResidueExteriorLift
  hπ data (s + 1) hs d (by dsimp; omega) hres a
local notation "C" => coefficientShearResidueAdjacentComponent
  hπ hm data s hs hk h3 h4 hc j

/-- The first scale-one adjacent zero is exactly the original exterior zero. -/
@[reassoc] theorem coefficientShearResidueZeroAdjacent_first :
    ProjectiveLine.zero Q ≫ C 0 = ProjectiveLine.zero Q ≫ F := by
  unfold coefficientShearResidueAdjacentComponent
  rw [dite_eq_right (by simp)]
  simp only [↓reduceIte]
  rw [← Category.assoc, coefficientShearScaleOneFirstComponent_zero, Category.assoc,
    Category.assoc, coefficientShearRetainedTensorChart_stageIso]
  let E := coefficientShearStageIso hπ data Q r
    (0 + 1 + s) (s + 1) (by omega) hs (by omega)
  have H := congrArg (· ≫ E.hom) (coefficientShearResidueZeroExteriorLift_zero
    hπ data (by omega) s (by omega) hres (lin).1 (lin).2 a ha)
  simp only [Category.assoc] at H
  rw [coefficientShearResidueExteriorLift_stageIso,
    coefficientShearRetainedScaleOneConic, Category.assoc,
    coefficientShearRetainedTensorChart_stageIso] at H
  exact H.symm

/-- The opposite scale-one adjacent zero is exactly the original exterior infinity. -/
@[reassoc] theorem coefficientShearResidueZeroAdjacent_second :
    ProjectiveLine.zero Q ≫ C 1 = ProjectiveLine.infinity Q ≫ F := by
  unfold coefficientShearResidueAdjacentComponent
  rw [dite_eq_right (by simp)]
  rw [ite_eq_right (by decide : (1 : Fin 2) ≠ 0)]
  rw [← Category.assoc, coefficientShearScaleOneSecondComponent_zero, Category.assoc,
    Category.assoc, coefficientShearRetainedTensorChart_stageIso]
  let E := coefficientShearStageIso hπ data Q r
    (0 + 1 + s) (s + 1) (by omega) hs (by omega)
  have H := congrArg (· ≫ E.hom) (coefficientShearResidueZeroExteriorLift_infinity
    hπ data (by omega) s (by omega) hres (lin).1 (lin).2 a ha)
  simp only [Category.assoc] at H
  rw [coefficientShearResidueExteriorLift_stageIso,
    coefficientShearRetainedScaleOneConic, Category.assoc,
    coefficientShearRetainedTensorChart_stageIso] at H
  exact H.symm

end FLT.Mazur.WeierstrassDividedDepth
