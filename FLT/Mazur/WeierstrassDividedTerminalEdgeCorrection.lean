/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFixedTerminalParameterIso
public import FLT.Mazur.WeierstrassDividedRetainedClosingIso

/-!
# Constructed full corrections between terminal and retained edge parameters

The inverse of each actual terminal substitution gives an exact correction
from the retained parameter. These corrections are allowed to be nontrivial;
a common global chart or gluing normalization is still a separate construction.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX WeierstrassDilatation
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] {W : WeierstrassCurve R} {π : R} {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "d" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "v" => arithmeticRetainedClosingUnit data H m (j + 1) hj
  (Fin.mk j (Nat.lt_succ_self j))
local notation "B" => Spec.map (CommRingCat.ofHom
  (AlgHom.toRingHom (LaurentUnitPoints.evalUnit (R := Q) v)))
local notation "T" => fixedTerminalPolygonBoundaryParameter data m j hj
  H.a1_unit (H.scale j) H.a2_div (H.b3_div _) (H.b4_div _) (H.b6_div _) u hu
local notation "E" => terminalArithmeticNodeEvaluation data m j hj
  H.a1_unit (H.scale j) H.a2_div (H.b3_div _) (H.b4_div _) (H.b6_div _)
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "P" => fixedTerminalPolygonIso π W (π ^ (1 + j + 1))
  (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit (H.scale (j + 1)) H.a2_div
  (H.b3_div _) (H.b4_div _) (H.b6_div _) u hu m

/-- Each actual terminal boundary has a constructed correction from the full retained unit. -/
def arithmeticTerminalEdgeCorrection (b : Bool) : branchTorus Q ≅ branchTorus Q :=
  asIso B ≪≫ (asIso (T b)).symm

/-- The correction is exact on the entire original Laurent scheme. -/
@[reassoc] theorem arithmeticTerminalEdgeCorrection_parameter (b : Bool) :
    (arithmeticTerminalEdgeCorrection data H m j hj u hu b).hom ≫ T b = B := by
  simp only [arithmeticTerminalEdgeCorrection, Iso.trans_hom, Iso.symm_hom,
    asIso_hom, asIso_inv, Category.assoc, IsIso.inv_hom_id, Category.comp_id]

/-- The corrected original full terminal node boundary has the retained closing parameter. -/
@[reassoc] theorem arithmeticTerminalEdgeCorrection_boundary (b : Bool) :
    (arithmeticTerminalEdgeCorrection data H m j hj u hu b).hom ≫
        Spec.map (CommRingCat.ofHom (E b).toRingHom) ≫ (P).hom =
      B ≫ (if b then leftBranchOpen Q τ else rightBranchOpen Q τ) := by
  rw [fixedTerminalPolygon_boundary data m j hj H.a1_unit (H.scale j) H.a2_div
    (H.b3_div _) (H.b4_div _) (H.b6_div _) u hu b]
  rw [← Category.assoc, arithmeticTerminalEdgeCorrection_parameter]

/-- Requiring no correction is equivalent to the original full parameter equality. -/
theorem arithmeticTerminalEdgeCorrection_eq_id_iff (b : Bool) :
    (arithmeticTerminalEdgeCorrection data H m j hj u hu b).hom = 𝟙 _ ↔ B = T b := by
  constructor
  · intro h
    have he := arithmeticTerminalEdgeCorrection_parameter data H m j hj u hu b
    rw [h, Category.id_comp] at he
    exact he.symm
  · intro h
    apply (cancel_mono (T b)).mp
    rw [arithmeticTerminalEdgeCorrection_parameter, h, Category.id_comp]

end FLT.Mazur.WeierstrassDividedDepth
