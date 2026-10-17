/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroFirstAtlasIdentification
public import FLT.Mazur.WeierstrassDividedZeroFirstTransitions

/-!
# Both full closing overlaps in the first depth-zero atlas

Use the same last-node factor as the initial edge and the same retained common
terminal. At layer one both complete closing overlaps are standard punctures.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticZeroFirstAtlasChart arithmeticFourthOuterAtlasChart arithmeticZeroFirstLastIso
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "ι" => arithmeticZeroFirstAtlasChart hπ data H m hj u hu
local notation "s" => arithmeticZeroFirstLastSmoothing hπ data H 0 hj u hu m
local notation "t" => arithmeticFourthTerminalSmoothing hπ data H 0 hj u hu m
local notation "K" => arithmeticZeroFirstLastEdgeIso hπ data H m 0 hj u hu

/-- Both installed closing overlaps retain their entire first corrected residual. -/
@[reassoc] theorem arithmeticZeroFirstAtlas_residual_closing (b : Bool) :
    (edgeInversion Q).hom ≫ leftBranchOpen Q (s b) ≫ ι (.retained ⟨0, by omega⟩ b) =
      (punctureSpecIso (arithmeticZeroFirstClosingEquiv hπ data H 0 hj u hu m b)).hom ≫
        punctureOpen t b ≫ ι .terminal := by
  apply (cancel_epi (K b).hom).mp
  rw [← arithmeticZeroFirstLastIso_closing_assoc, arithmeticZeroFirstLast_chart]
  have h := arithmeticFourthOuterAtlas_residual_closing hπ data H m 0 hj u hu b
  simp only [Category.assoc] at h
  rw [h]
  simp only [arithmeticZeroFirstClosingEquiv, punctureSpecIso_trans, punctureSpecIso_symm,
    arithmeticZeroFirstLastEdgeEquiv_spec, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.hom_inv_id_assoc, arithmeticFourthClosingEquiv_spec,
    arithmeticZeroFirstAtlasChart_terminal]

omit m in
/-- Both complete closing overlaps are standard on the first arithmetic layer. -/
@[reassoc] theorem arithmeticZeroFirstAtlas_closing_first (b : Bool) :
    (edgeInversion (Quotient R π 1)).hom ≫
        leftBranchOpen (Quotient R π 1)
          (arithmeticZeroFirstLastSmoothing hπ data H 0 hj u hu 1 b) ≫
          arithmeticZeroFirstAtlasChart hπ data H 1 hj u hu (.retained ⟨0, by omega⟩ b) =
      punctureOpen (arithmeticFourthTerminalSmoothing hπ data H 0 hj u hu 1) b ≫
        arithmeticZeroFirstAtlasChart hπ data H 1 hj u hu .terminal := by
  rw [arithmeticZeroFirstAtlas_residual_closing, arithmeticZeroFirstClosingEquiv_first,
    punctureSpecIso_refl, Iso.refl_hom, Category.id_comp]

end FLT.Mazur.WeierstrassDividedDepth
