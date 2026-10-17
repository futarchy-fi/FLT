/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFifthFartherEndIdentification
public import FLT.Mazur.WeierstrassDividedFifthShallowTransitions
public import FLT.Mazur.WeierstrassDividedFifthShallowTerminalGeometry
public import FLT.Mazur.WeierstrassDividedFourthOuterAtlasClosing

/-!
# Actual closing squares in the installed depth-three fifth atlas

The last retained label is identified with its unchanged smoothing. The
terminal label keeps the exact fifth rebased smoothing at every order.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticFifthShallowLastOrientedIso arithmeticFifthFartherAtlasChart
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u) (ha₃ : 3 = j)
local notation "Q" => Quotient R π m
local notation "ι" => arithmeticFifthFartherAtlasChart hπ data H m j hj u hu ha₃
local notation "κ" => arithmeticFourthOuterAtlasChart hπ data H m j hj u hu
local notation "O" => twistedRetainedOrientation data H m
local notation "L" => arithmeticClosingRetainedBoundary data H m
local notation "s" => arithmeticFifthShallowTerminalSmoothing hπ data H j hj u hu m
local notation "N" => arithmeticFourthOuterLastIdentification hπ data H m j hj u hu
local notation "D" => arithmeticFifthFartherLastIdentification hπ data H m j hj u hu
local notation "t" => arithmeticFourthTerminalSmoothing hπ data H j hj u hu m

/-- Both actual closing overlaps have the complete fifth algebraic residual. -/
@[reassoc] theorem arithmeticFifthFartherAtlas_residual_closing (b : Bool) :
    (L ≫ (O b).hom) ≫ (D b).hom ≫ ι (.retained ⟨j, by omega⟩ b) =
      (punctureSpecIso (arithmeticFifthShallowClosingEquiv hπ data H j hj u hu m b)).hom ≫
        punctureOpen s b ≫ ι .terminal := by
  apply (cancel_epi (arithmeticFifthShallowLastEdgeIso hπ data H m j hj u hu b true).hom).mp
  calc
    _ = (L ≫ (O b).hom) ≫ (N b).hom ≫ κ (.retained ⟨j, by omega⟩ b) := by
      rw [← Category.assoc _ (L ≫ (O b).hom),
        ← arithmeticFifthShallowLastOrientedIso_closing, Category.assoc,
        arithmeticFifthFartherLast_chart]
    _ = (arithmeticFourthClosingResidual hπ data H m j hj u hu b).hom ≫
        punctureOpen t b ≫ κ .terminal :=
      arithmeticFourthOuterAtlas_residual_closing hπ data H m j hj u hu b
    _ = _ := by
      simp only [arithmeticFifthShallowClosingEquiv, punctureSpecIso_trans,
        punctureSpecIso_symm, arithmeticFifthShallowLastEdgeEquiv_spec,
        arithmeticFourthClosingEquiv_spec, Iso.trans_hom, Iso.symm_hom,
        Category.assoc, Iso.hom_inv_id_assoc]
      have ht := arithmeticFifthShallowTerminalIso_puncture hπ data H j hj u hu m b
      simp only [punctureSpecIso_symm, Iso.symm_hom] at ht
      rw [← Category.assoc _ (punctureOpen s b), ← ht, Category.assoc,
        arithmeticFifthFartherTerminal_chart]

omit m in
/-- Both installed closing residuals disappear at layer five. -/
@[reassoc] theorem arithmeticFifthFartherAtlas_closing_fifth (b : Bool) :
    (arithmeticClosingRetainedBoundary data H 5 ≫
        (twistedRetainedOrientation data H 5 b).hom) ≫
      (arithmeticFifthFartherLastIdentification hπ data H 5 j hj u hu b).hom ≫
        arithmeticFifthFartherAtlasChart hπ data H 5 j hj u hu ha₃ (.retained ⟨j, by omega⟩ b) =
      punctureOpen (arithmeticFifthShallowTerminalSmoothing hπ data H j hj u hu 5) b ≫
        arithmeticFifthFartherAtlasChart hπ data H 5 j hj u hu ha₃ .terminal := by
  rw [arithmeticFifthFartherAtlas_residual_closing, arithmeticFifthShallowClosingEquiv_fifth,
    punctureSpecIso_refl, Iso.refl_hom]
  exact Category.id_comp _

end FLT.Mazur.WeierstrassDividedDepth
