/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFifthShallowAtlasIdentification
public import FLT.Mazur.WeierstrassDividedFifthShallowTransitions
public import FLT.Mazur.WeierstrassDividedFifthShallowTerminalGeometry
public import FLT.Mazur.WeierstrassDividedFourthShallowAtlasClosing

/-!
# Actual closing squares in the installed fifth depth-two atlas

The last retained label is identified with its unchanged smoothing. The
terminal label keeps the exact fifth rebased smoothing at every order.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticFifthShallowLastOrientedIso arithmeticFifthShallowAtlasChart
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 3 ≤ n)
  (u : Rˣ) (hu : (data ⟨3, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "ι" => arithmeticFifthShallowAtlasChart hπ data H m hj u hu
local notation "κ" => arithmeticFourthShallowAtlasChart hπ data H m 2 hj u hu
local notation "O" => twistedRetainedOrientation data H m
local notation "L" => arithmeticClosingRetainedBoundary data H m
local notation "s" => arithmeticFifthShallowTerminalSmoothing hπ data H 2 hj u hu m
local notation "N" => arithmeticFourthShallowLastIdentification hπ data H m 2 hj u hu
local notation "t" => arithmeticFourthTerminalSmoothing hπ data H 2 hj u hu m

/-- Both actual closing overlaps have the complete fifth algebraic residual. -/
@[reassoc] theorem arithmeticFifthShallowAtlas_residual_closing (b : Bool) :
    (L ≫ (O b).hom) ≫ ι (.retained ⟨2, by omega⟩ b) =
      (punctureSpecIso (arithmeticFifthShallowClosingEquiv hπ data H 2 hj u hu m b)).hom ≫
        punctureOpen s b ≫ ι .terminal := by
  apply (cancel_epi (arithmeticFifthShallowLastEdgeIso hπ data H m 2 hj u hu b true).hom).mp
  calc
    _ = (L ≫ (O b).hom) ≫ (N b).hom ≫ κ (.retained ⟨2, by omega⟩ b) := by
      rw [← Category.assoc _ (L ≫ (O b).hom),
        ← arithmeticFifthShallowLastOrientedIso_closing, Category.assoc,
        arithmeticFifthShallowLast_chart]
    _ = (arithmeticFourthClosingResidual hπ data H m 2 hj u hu b).hom ≫
        punctureOpen t b ≫ κ .terminal :=
      arithmeticFourthShallowAtlas_residual_closing hπ data H m 2 hj u hu b
    _ = _ := by
      simp only [arithmeticFifthShallowClosingEquiv, punctureSpecIso_trans,
        punctureSpecIso_symm, arithmeticFifthShallowLastEdgeEquiv_spec,
        arithmeticFourthClosingEquiv_spec, Iso.trans_hom, Iso.symm_hom,
        Category.assoc, Iso.hom_inv_id_assoc]
      have ht := arithmeticFifthShallowTerminalIso_puncture hπ data H 2 hj u hu m b
      simp only [punctureSpecIso_symm, Iso.symm_hom] at ht
      rw [← Category.assoc _ (punctureOpen s b), ← ht, Category.assoc,
        arithmeticFifthShallowTerminal_chart]

omit m in
/-- Both installed closing residuals disappear at layer five. -/
@[reassoc] theorem arithmeticFifthShallowAtlas_closing_fifth (b : Bool) :
    (arithmeticClosingRetainedBoundary data H 5 ≫
        (twistedRetainedOrientation data H 5 b).hom) ≫
      arithmeticFifthShallowAtlasChart hπ data H 5 hj u hu (.retained ⟨2, by omega⟩ b) =
      punctureOpen (arithmeticFifthShallowTerminalSmoothing hπ data H 2 hj u hu 5) b ≫
        arithmeticFifthShallowAtlasChart hπ data H 5 hj u hu .terminal := by
  rw [arithmeticFifthShallowAtlas_residual_closing, arithmeticFifthShallowClosingEquiv_fifth,
    punctureSpecIso_refl, Iso.refl_hom]
  exact Category.id_comp _

end FLT.Mazur.WeierstrassDividedDepth
