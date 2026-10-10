/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedInitialBoundaryGeometry
public import FLT.Mazur.WeierstrassDividedInitialTensorBoundary
public import FLT.Mazur.WeierstrassDividedOlderGlobalComponentSections

/-!
# Signed reciprocal overlap of the full initial parameters and first retained lines

The original tensor boundary equality restricts to both original conic punctures
in every retained global stage. This is an equality of actual scheme morphisms.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (h1 : 1 ≤ n)
  (hstart : 0 < start) (hk : 2 * (start + 1) ≤ depth)
  (r : ℕ) (hr : 1 + r ≤ n)
open WeierstrassModificationX WeierstrassSuccessiveX
local notation "K" => ResidueField R
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "a" => residue R W.a₁
local notation "c" => residue R (Data.b6 d)
local notation "hc" => Iff.mpr (residue_eq_zero_iff _)
  (WeierstrassDilatation.divided_constant_mem D start (by omega)
    (Data.b6 d) (Data.factor6 d))
local notation "ha" => residue_tangent_isUnit D
local notation "tangent" => WeierstrassDilatation.residueTangentUnit D
local notation "p" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom (conicZeroPuncture c hc)))
local notation "ρ₁" => Spec.map (CommRingCat.ofHom
  (AlgHom.toRingHom (PolygonScaledReciprocal.reciprocal (tangent)⁻¹)))
local notation "ρ₂" => Spec.map (CommRingCat.ofHom
  (AlgHom.toRingHom (PolygonScaledReciprocal.reciprocal (-tangent)⁻¹)))
local notation "P₁" => initialGlobalConicFirstParameter hπ data D (1 + r) hr hstart (by omega)
local notation "P₂" => initialGlobalConicSecondParameter hπ data D (1 + r) hr hstart (by omega)
local notation "G₁" => olderGlobalMiddleFirstLine hπ data D 0 h1 r hr hstart hk
local notation "G₂" => olderGlobalMiddleSecondLine hπ data D 0 h1 r hr hstart hk

/-- The first full initial parameter meets the first retained line with its original scale. -/
@[reassoc] theorem initialGlobalFirstParameter_overlap :
    p ≫ P₁ = ρ₁ ≫ ProjectiveLine.overlapLeft K ≫ G₁ := by
  rw [initialGlobalConicFirstParameter]
  simp only [← Category.assoc]
  have H := conicPuncturedFirst_spec c hc (W.map (residue R)) ha
  simp only [WeierstrassCurve.map] at H
  rw [← Category.assoc] at H
  rw [← H]
  simp only [initialGlobalConic, initialGlobalResidueFiberChart, Category.assoc]
  erw [initialConicFirstLine_boundary_spec_assoc hπ data D h1 hstart hk]
  rw [initialRetainedGlobalTensor_boundary hπ data K h1 r hr]
  simp only [Iso.hom_inv_id_assoc]
  rw [residueLineToHorizontal_comp_assoc]
  rfl

/-- The opposite initial parameter retains the negative reciprocal scale on the first line. -/
@[reassoc] theorem initialGlobalSecondParameter_overlap :
    p ≫ P₂ = ρ₂ ≫ ProjectiveLine.overlapLeft K ≫ G₂ := by
  rw [initialGlobalConicSecondParameter]
  simp only [← Category.assoc]
  have H := conicPuncturedSecond_spec c hc (W.map (residue R)) ha
  simp only [WeierstrassCurve.map] at H
  rw [← Category.assoc] at H
  rw [← H]
  simp only [initialGlobalConic, initialGlobalResidueFiberChart, Category.assoc]
  erw [initialConicSecondLine_boundary_spec_assoc hπ data D h1 hstart hk]
  rw [initialRetainedGlobalTensor_boundary hπ data K h1 r hr]
  simp only [Iso.hom_inv_id_assoc]
  rw [residueLineToHorizontal_comp_assoc]
  rfl

end FLT.Mazur.WeierstrassDividedDepth
