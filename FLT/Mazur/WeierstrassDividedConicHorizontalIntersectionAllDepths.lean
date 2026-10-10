/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedConicBoundaryGeometryAllDepths
public import FLT.Mazur.WeierstrassSuccessiveXResidueLineHorizontal

/-!
# Ordered punctures are full intersections with the next horizontal lines

Transport the original line-horizontal pullbacks by the actual conic boundary
and scaled reciprocal isomorphisms. This includes preceding depth zero;
no line origin belongs to this boundary.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (hk : 2 * (start + j + 1) ≤ depth)
  (hjNext : j + 2 ≤ n) (hkNext : 2 * (start + (j + 1) + 1) ≤ depth)
open WeierstrassSuccessiveX
local notation "K" => ResidueField R
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "fData" => data (Fin.mk (j + 2) (Nat.lt_succ_of_le hjNext))
local notation "W₀" => W.map (residue R)
local notation "c" => residue R (Data.b6 e)
local notation "ha" => D.a₁_unit.map (residue R)
local notation "hc" => Iff.mpr (residue_eq_zero_iff _)
  (WeierstrassDilatation.divided_constant_mem D (start + j + 1) (by omega)
    (Data.b6 e) (Data.factor6 e))
local notation "s₁" => Spec.map (CommRingCat.ofHom
  (AlgHom.toRingHom (conicBoundaryFirst W₀ c ha hc)))
local notation "s₂" => Spec.map (CommRingCat.ofHom
  (AlgHom.toRingHom (conicBoundarySecond W₀ c ha hc)))
local notation "copen" => residueDividedConicOpenEquiv D (start + j) hk
  (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e)
local notation "q" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom (AlgEquiv.toAlgHom copen)))
local notation "x" => WeierstrassDilatation.x W (π ^ (start + j + 1))
  (Data.b3 e) (Data.b4 e) (Data.b6 e)
local notation "t" => coord W (π ^ (start + j)) π (Data.b3 e) (Data.b4 e) (Data.b6 e) 0
local notation "uNext" => coord W (π ^ (start + (j + 1))) π
  (Data.b3 fData) (Data.b4 fData) (Data.b6 fData) 2
local notation "B" => PrincipalOpenTensor.transitionIso K x uNext
  (previousBoundaryEquiv hπ e fData)
local notation "LNext" => residueLineToHorizontal D (start + (j + 1)) (by omega) hkNext
  (Data.b3 fData) (Data.b4 fData) (Data.b6 fData) (Data.factor3 fData) (Data.factor4 fData)
local notation "tangent" => WeierstrassDilatation.residueTangentUnit D
local notation "ρ₁" => Spec.map (CommRingCat.ofHom
  (AlgHom.toRingHom (PolygonScaledReciprocal.reciprocal (tangent)⁻¹)))
local notation "ρ₂" => Spec.map (CommRingCat.ofHom
  (AlgHom.toRingHom (PolygonScaledReciprocal.reciprocal (-tangent)⁻¹)))
local notation "p" => ProjectiveLine.overlapLeft K

local notation "L" => residueSuccessiveLineImmersion D (start + (j + 1)) (by omega) hkNext
  (Data.b3 fData) (Data.b4 fData) (Data.b6 fData) (Data.factor3 fData) (Data.factor4 fData)

/-- The first conic puncture is the entire intersection with its next ordered line. -/
theorem adjacentConicFirstHorizontal_isPullback_anyDepth :
    IsPullback s₁ (ρ₁ ≫ p)
      (q ≫ (B).inv ≫ PrincipalOpenTensor.inclusion K uNext) (L 0 (by simp)) := by
  let Q := Scheme.Spec.mapIso (copen).toRingEquiv.toCommRingCatIso.op
  let I := Scheme.Spec.mapIso
    (PolygonScaledReciprocal.equiv (tangent)⁻¹).toRingEquiv.toCommRingCatIso.op
  apply (residueLineHorizontal_isPullback D (start + (j + 1)) (by omega) hkNext
    (Data.b3 fData) (Data.b4 fData) (Data.b6 fData)
    (Data.factor3 fData) (Data.factor4 fData) 0 (by simp)).of_iso'
      I (Q ≪≫ (B).symm) (Iso.refl _) (Iso.refl _)
  · change ρ₁ ≫ LNext 0 (by simp) = s₁ ≫ q ≫ (B).inv
    rw [← Category.assoc, adjacentConicFirstLine_boundary_spec_anyDepth hπ data D j hj hk
      hjNext hkNext]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  · change ρ₁ ≫ p = (ρ₁ ≫ p) ≫ 𝟙 _
    rw [Category.comp_id]
  · simp only [Iso.trans_hom, Iso.symm_hom, Iso.refl_hom, Category.comp_id, Category.assoc]
    rfl
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]

/-- The second conic puncture is the entire intersection with its next ordered line. -/
theorem adjacentConicSecondHorizontal_isPullback_anyDepth :
    IsPullback s₂ (ρ₂ ≫ p)
      (q ≫ (B).inv ≫ PrincipalOpenTensor.inclusion K uNext) (L (-residue R W.a₁) (by simp)) := by
  let Q := Scheme.Spec.mapIso (copen).toRingEquiv.toCommRingCatIso.op
  let I := Scheme.Spec.mapIso
    (PolygonScaledReciprocal.equiv (-tangent)⁻¹).toRingEquiv.toCommRingCatIso.op
  apply (residueLineHorizontal_isPullback D (start + (j + 1)) (by omega) hkNext
    (Data.b3 fData) (Data.b4 fData) (Data.b6 fData)
    (Data.factor3 fData) (Data.factor4 fData) (-residue R W.a₁) (by simp)).of_iso'
      I (Q ≪≫ (B).symm) (Iso.refl _) (Iso.refl _)
  · change ρ₂ ≫ LNext (-residue R W.a₁) (by simp) = s₂ ≫ q ≫ (B).inv
    rw [← Category.assoc, adjacentConicSecondLine_boundary_spec_anyDepth hπ data D j hj hk
      hjNext hkNext]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  · change ρ₂ ≫ p = (ρ₂ ≫ p) ≫ 𝟙 _
    rw [Category.comp_id]
  · simp only [Iso.trans_hom, Iso.symm_hom, Iso.refl_hom, Category.comp_id, Category.assoc]
    rfl
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]

end FLT.Mazur.WeierstrassDividedDepth
