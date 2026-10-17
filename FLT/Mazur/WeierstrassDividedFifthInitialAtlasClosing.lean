/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFifthInitialAtlasIdentification
public import FLT.Mazur.WeierstrassDividedFifthInitialTransitions
public import FLT.Mazur.WeierstrassDividedFifthShallowTerminalGeometry
public import FLT.Mazur.WeierstrassDividedFourthInitialAtlasClosing

/-!
# Actual closing squares in the installed fifth depth-one atlas

The last retained label is identified with its unchanged smoothing. The
terminal label keeps the exact fifth rebased smoothing at every order.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticFifthInitialLastOrientedIso arithmeticFifthInitialAtlasChart
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 2 ≤ n)
  (u : Rˣ) (hu : (data ⟨2, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "ι" => arithmeticFifthInitialAtlasChart hπ data H m hj u hu
local notation "κ" => arithmeticFourthInitialAtlasChart hπ data H m 1 hj u hu
local notation "O" => twistedRetainedOrientation data H m
local notation "L" => arithmeticClosingRetainedBoundary data H m
local notation "s" => arithmeticFifthShallowTerminalSmoothing hπ data H 1 hj u hu m
local notation "N" => arithmeticFourthInitialLastIdentification hπ data H m 1 hj u hu
local notation "t" => arithmeticFourthTerminalSmoothing hπ data H 1 hj u hu m

/-- Both actual closing overlaps have the complete fifth algebraic residual. -/
@[reassoc] theorem arithmeticFifthInitialAtlas_residual_closing (b : Bool) :
    (L ≫ (O b).hom) ≫ ι (.retained ⟨1, by omega⟩ b) =
      (punctureSpecIso (arithmeticFifthInitialClosingEquiv hπ data H 1 hj u hu m b)).hom ≫
        punctureOpen s b ≫ ι .terminal := by
  apply (cancel_epi (arithmeticFifthInitialLastEdgeIso hπ data H m 1 hj u hu b true).hom).mp
  calc
    _ = (L ≫ (O b).hom) ≫ (N b).hom ≫ κ (.retained ⟨1, by omega⟩ b) := by
      rw [← Category.assoc _ (L ≫ (O b).hom),
        ← arithmeticFifthInitialLastOrientedIso_closing, Category.assoc,
        arithmeticFifthInitialLast_chart]
    _ = (arithmeticFourthClosingResidual hπ data H m 1 hj u hu b).hom ≫
        punctureOpen t b ≫ κ .terminal :=
      arithmeticFourthInitialAtlas_residual_closing hπ data H m 1 hj u hu b
    _ = _ := by
      simp only [arithmeticFifthInitialClosingEquiv, punctureSpecIso_trans,
        punctureSpecIso_symm, arithmeticFifthInitialLastEdgeEquiv_spec,
        arithmeticFourthClosingEquiv_spec, Iso.trans_hom, Iso.symm_hom,
        Category.assoc, Iso.hom_inv_id_assoc]
      have ht := arithmeticFifthShallowTerminalIso_puncture hπ data H 1 hj u hu m b
      simp only [punctureSpecIso_symm, Iso.symm_hom] at ht
      rw [← Category.assoc _ (punctureOpen s b), ← ht, Category.assoc,
        arithmeticFifthInitialTerminal_chart]

omit m in
/-- Both installed closing residuals disappear at layer five. -/
@[reassoc] theorem arithmeticFifthInitialAtlas_closing_fifth (b : Bool) :
    (arithmeticClosingRetainedBoundary data H 5 ≫
        (twistedRetainedOrientation data H 5 b).hom) ≫
      arithmeticFifthInitialAtlasChart hπ data H 5 hj u hu (.retained ⟨1, by omega⟩ b) =
      punctureOpen (arithmeticFifthShallowTerminalSmoothing hπ data H 1 hj u hu 5) b ≫
        arithmeticFifthInitialAtlasChart hπ data H 5 hj u hu .terminal := by
  rw [arithmeticFifthInitialAtlas_residual_closing, arithmeticFifthInitialClosingEquiv_fifth,
    punctureSpecIso_refl, Iso.refl_hom]
  exact Category.id_comp _

end FLT.Mazur.WeierstrassDividedDepth
