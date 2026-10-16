/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTerminalEdgeCorrection
public import FLT.Mazur.WeierstrassDividedFixedTerminalRestriction
public import FLT.Mazur.WeierstrassDividedRetainedClosingRestriction

/-!
# Restriction of both full terminal edge corrections

The actual correction isomorphisms and their inverses commute with every
consecutive arithmetic quotient arrow. This uses the full parameter squares
and uniqueness of the inverses, with no altered source gluing.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX WeierstrassDilatation
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R} {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (hπ : π ≠ 0) (m j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "ρ" => Spec.map (CommRingCat.ofHom
  (PolygonScalingNaturality.coeffMap (AlgHom.toRingHom (restriction R π m))))
local notation "C" => fun a b ↦ arithmeticTerminalEdgeCorrection data H a j hj u hu b
include hπ

/-- The full correction preserves the original consecutive coefficient arrows. -/
@[reassoc] theorem arithmeticTerminalEdgeCorrection_restriction (b : Bool) :
    ρ ≫ (C (m + 1) b).hom = (C m b).hom ≫ ρ := by
  simp only [arithmeticTerminalEdgeCorrection, Iso.trans_hom, Iso.symm_hom,
    asIso_hom, asIso_inv]
  rw [← Category.assoc, arithmeticRetainedClosingParameter_restriction,
    Category.assoc, fixedTerminalPolygonBoundaryParameter_inv_restriction R π m
      H.a1_unit hπ, ← Category.assoc]

/-- Its inverse is compatible with the same original arrows. -/
@[reassoc] theorem arithmeticTerminalEdgeCorrection_inv_restriction (b : Bool) :
    ρ ≫ (C (m + 1) b).inv = (C m b).inv ≫ ρ := by
  apply (cancel_mono (C (m + 1) b).hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id,
    Category.assoc, arithmeticTerminalEdgeCorrection_restriction data H hπ,
    ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

end FLT.Mazur.WeierstrassDividedDepth
