/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearRootStrictPositiveCoordinateComponents
public import FLT.Mazur.WeierstrassCoefficientShearInitialCompleteOriginal
public import FLT.Mazur.WeierstrassCoefficientShearInitialCompleteRootChange

/-!
# The independent full companion exterior in opposite strict coordinates

The opposite exterior is the independently extended root-sheared incidence
line with its actual signed slope normalization, including the point at infinity.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hstart : 0 < start) (hk : 2 * (start + s + 1) ≤ depth)
  (hp : 2 * (start + s + 1) < depth)
open WeierstrassDilatation WeierstrassModificationX
local notation "K" => ResidueField R
local notation "d" => data ⟨0, Nat.zero_lt_succ n⟩
local notation "hscale" => residue_scale_eq_zero D start hstart
local notation "h3" => Iff.mpr (residue_eq_zero_iff _)
  (And.left (divided_linear_mem D start (by omega)
    (Data.b3 d) (Data.b4 d) (Data.factor3 d) (Data.factor4 d)))
local notation "h4" => Iff.mpr (residue_eq_zero_iff _)
  (And.right (divided_linear_mem D start (by omega)
    (Data.b3 d) (Data.b4 d) (Data.factor3 d) (Data.factor4 d)))
local notation "a" => residueTangentUnit D
local notation "ha" => Eq.trans (residueTangentUnit_val D)
  (Eq.symm (rootShearZero_tangent (W.map (residue R))))
local notation "t" => -algebraMap R K W.a₁
local notation "h0" => show (0 : K) ^ 2 + algebraMap R K W.a₁ * 0 -
    algebraMap R K W.a₂ = 0 from by
  rw [zero_pow (by decide : 2 ≠ 0), mul_zero, zero_add, zero_sub, neg_eq_zero]
  exact (residue_eq_zero_iff _).mpr D.a₂_mem
local notation "ht" => show (t : K) ^ 2 + algebraMap R K W.a₁ * t -
    algebraMap R K W.a₂ = 0 from by
  have h2 : algebraMap R K W.a₂ = 0 := (residue_eq_zero_iff _).mpr D.a₂_mem
  rw [h2]
  ring
local notation "N0" => coefficientShearInitialCompleteNormalization
  hπ data K 0 (s + 1) hs hscale h3 h4 h0
local notation "Nt" => coefficientShearInitialCompleteNormalization
  hπ data K t (s + 1) hs hscale h3 h4 ht
local notation "O" => coefficientShearRootStrictPositiveOppositeCoordinates
  hπ data D s hs hstart hk hp t
local notation "PN" => (PolygonAtlas.normalization K (2 * s + 5)).left

/-- Construct the companion exterior independently from its full incidence line and properness. -/
def coefficientShearRootStrictPositiveCompanionExterior :
    ProjectiveLine.scheme K ⟶ coefficientShearGlued hπ data K t (s + 1) hs :=
  (ProjectiveLine.slopeNormalizationIso (-a)).inv ≫ Nt

/-- The complete opposite exterior is the independently normalized companion-root construction. -/
@[reassoc] theorem coefficientShearRootStrictPositiveOppositeCoordinates_independentExterior :
    (PolygonPinching.componentι K (2 * s + 5) 0).left ≫ PN ≫ (O).hom =
      coefficientShearRootStrictPositiveCompanionExterior hπ data D s hs hstart hp := by
  rw [coefficientShearRootStrictPositiveOppositeCoordinates_exterior]
  change ProjectiveLine.endpointReversal K ≫
    initialOrientedToGlobal hπ data D (s + 1) hs hstart (by omega) (by omega) ≫
      (coefficientShearGluedIso hπ data K 0 (s + 1) hs).inv ≫ _ = _
  rw [← coefficientShearInitialCompleteNormalization_ordered_original
    hπ data D (s + 1) hs hstart (by omega) (by omega) hscale h3 h4 h0]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  exact coefficientShearInitialCompleteNormalization_opposite
    hπ data K 0 t (s + 1) hs hscale h3 h4 h0 ht a ha (zero_add t)

/-- The independently normalized companion exterior retains the actual residue-field map. -/
@[reassoc] theorem coefficientShearRootStrictPositiveCompanionExterior_structure :
    coefficientShearRootStrictPositiveCompanionExterior hπ data D s hs hstart hp ≫
        coefficientShearGluedStructure hπ data K t (s + 1) hs = ProjectiveLine.toBase K := by
  rw [coefficientShearRootStrictPositiveCompanionExterior, Category.assoc,
    coefficientShearInitialCompleteNormalization_structure,
    ProjectiveLine.slopeNormalizationIso_inv_base]

end FLT.Mazur.WeierstrassDividedDepth
