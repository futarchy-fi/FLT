/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTensorIntegralAtlas
public import FLT.Mazur.WeierstrassDividedTensorAtlasComparison
public import FLT.Mazur.WeierstrassDividedTerminalLowerCoordinates
public import FLT.Mazur.WeierstrassDilatationResidueRetained

/-!
# The full terminal tensor comparison retains the integral coordinates

Undoing the terminal atlas indexing is the original tensor projection.
Consequently both coordinate prime tests agree without passing to a field.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [IsDomain R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type) [CommRing S] [Algebra R S] (j : ℕ) (hj : j ≤ n)
local notation "e" => data ⟨j, Nat.lt_succ_of_le hj⟩
local notation "T" => ScalarExtension W (π ^ (start + j)) (e).b3 (e).b4 (e).b6 S
local notation "E" => finiteDividedTensorAtlasIso hπ data S j hj
local notation "coords" => tensorIntegralAtlasProjection hπ data S j hj (1 : Fin (j + 3))
local notation "proj" => (TensorOpenChart.projection : Spec (.of T) ⟶ chart e)

/-- The terminal tensor indexing preserves the whole integral projection. -/
@[reassoc] theorem terminalTensorAtlasIso_projection : (E).hom ≫ coords = proj := by
  change (E).hom ≫ pullback.fst _ _ = _
  exact (finiteDividedTensorChart_isPullback hπ data S j hj).flip.isoPullback_hom_fst

/-- Undoing the atlas comparison recovers the same original terminal coordinates. -/
@[reassoc] theorem terminalTensorAtlasIso_inv_projection : (E).inv ≫ proj = coords := by
  rw [← terminalTensorAtlasIso_projection, Iso.inv_hom_id_assoc]

/-- Horizontal prime membership agrees in the full original tensor chart. -/
theorem terminalTensorAtlasProjection_x_iff
    (p : globalTensorAtlasObject hπ data S j hj (1 : Fin (j + 3))) :
    x W (π ^ (start + j)) (e).b3 (e).b4 (e).b6 ∈ (coords p).asIdeal ↔
      tensorX W (π ^ (start + j)) (e).b3 (e).b4 (e).b6 S ∈ ((E).inv p).asIdeal := by
  rw [← terminalTensorAtlasIso_inv_projection]
  rfl

/-- Vertical prime membership also agrees before any specialization or reduction. -/
theorem terminalTensorAtlasProjection_y_iff
    (p : globalTensorAtlasObject hπ data S j hj (1 : Fin (j + 3))) :
    y W (π ^ (start + j)) (e).b3 (e).b4 (e).b6 ∈ (coords p).asIdeal ↔
      tensorY W (π ^ (start + j)) (e).b3 (e).b4 (e).b6 S ∈ ((E).inv p).asIdeal := by
  rw [← terminalTensorAtlasIso_inv_projection]
  rfl

end FLT.Mazur.WeierstrassDividedDepth
