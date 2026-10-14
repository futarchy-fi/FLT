/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearRootStrictPositiveCoordinateComponents
public import FLT.Mazur.WeierstrassCoefficientShearRootTerminalRootChange
import all FLT.Mazur.WeierstrassCoefficientShearRootFinalTerminal

/-!
# Independent companion-root terminal components in opposite polygon coordinates

Both terminal positions in the explicit opposite coordinates are identified
with their independently glued complete projective lines at the companion root.
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
local notation "d" => data ⟨s + 1, Nat.lt_succ_of_le hs⟩
local notation "hprev" => show 0 < start + s from by omega
local notation "hscale" => residue_scale_eq_zero D (start + s) hprev
local notation "hπ₀" => Iff.mpr (residue_eq_zero_iff π)
  (D.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self π)
local notation "h3" => Iff.mpr (residue_eq_zero_iff _)
  (And.left (divided_linear_mem D (start + (s + 1)) hk
    (Data.b3 d) (Data.b4 d) (Data.factor3 d) (Data.factor4 d)))
local notation "h4" => Iff.mpr (residue_eq_zero_iff _)
  (And.right (divided_linear_mem D (start + (s + 1)) hk
    (Data.b3 d) (Data.b4 d) (Data.factor3 d) (Data.factor4 d)))
local notation "h6" => Iff.mpr (residue_eq_zero_iff _)
  (divided_constant_mem D (start + (s + 1)) hp (Data.b6 d) (Data.factor6 d))
local notation "hroot" => show (0 : K) ^ 2 + algebraMap R K W.a₁ * 0 -
    algebraMap R K W.a₂ = 0 from by
  rw [zero_pow (by decide : 2 ≠ 0), mul_zero, zero_add, zero_sub, neg_eq_zero]
  exact (residue_eq_zero_iff _).mpr D.a₂_mem
local notation "a" => residueTangentUnit D
local notation "ha" => Eq.trans (residueTangentUnit_val D)
  (Eq.symm (rootShearZero_tangent (W.map (residue R))))
variable (t : ResidueField R) (b : (ResidueField R)ˣ)
  (hb : (b : ResidueField R) =
    (rootShearCurve (W.map (algebraMap R (ResidueField R))) t).a₁)
  (ht : t ^ 2 + algebraMap R (ResidueField R) W.a₁ * t -
    algebraMap R (ResidueField R) W.a₂ = 0)
  (hrt : 0 + t = -algebraMap R (ResidueField R) W.a₁)
local notation "C" => coefficientShearRootChange hπ data K 0 t (s + 1) hs
local notation "T₁" => coefficientShearRootTerminalFirstComponent
  hπ data K t s hs hscale hπ₀ h3 h4 h6 ht b hb
local notation "T₂" => coefficientShearRootTerminalSecondComponent
  hπ data K t s hs hscale hπ₀ h3 h4 h6 ht b hb
local notation "B" => coefficientShearRootStrictPositiveBranchComponent
  hπ data D s hs hstart hk hp
local notation "O" => coefficientShearRootStrictPositiveOppositeCoordinates
  hπ data D s hs hstart hk hp t
local notation "PN" => (PolygonAtlas.normalization K (2 * s + 5)).left
include hstart hrt

/-- The original first terminal component changes to the independently glued companion second. -/
@[reassoc] theorem coefficientShearRootStrictPositiveTerminal_first_rootChange :
    coefficientShearRootFinalTerminalComponent hπ data D s hs hk hp 0 ≫ (C).hom = T₂ := by
  simp only [coefficientShearRootFinalTerminalComponent, dite_eq_left hprev, Fin.cases_zero]
  exact coefficientShearRootTerminalFirstComponent_rootChange
    hπ data K 0 s hs hscale hπ₀ h3 h4 h6 hroot a ha t ht b hb hrt

/-- The original second terminal component changes to the independently glued companion first. -/
@[reassoc] theorem coefficientShearRootStrictPositiveTerminal_second_rootChange :
    coefficientShearRootFinalTerminalComponent hπ data D s hs hk hp 1 ≫ (C).hom = T₁ := by
  simp only [coefficientShearRootFinalTerminalComponent, dite_eq_left hprev]
  exact coefficientShearRootTerminalSecondComponent_rootChange
    hπ data K 0 s hs hscale hπ₀ h3 h4 h6 hroot a ha t ht b hb hrt

omit hrt in
/-- The last edge in either chain is precisely its independent complete terminal component. -/
theorem coefficientShearRootStrictPositiveBranchComponent_terminal (i : Fin 2) :
    B ⟨s + 1, by omega⟩ i =
      coefficientShearRootFinalTerminalOverComponent hπ data D s hs hk hp i := by
  rw [coefficientShearRootStrictPositiveBranchComponent,
    dite_eq_right (show ¬s + 1 = 0 by omega)]
  simp only [coefficientShearRootFinalBranchComponent, Nat.add_sub_cancel,
    lt_self_iff_false, dite_false]

/-- The first terminal polygon position is its actual companion-root projective component. -/
@[reassoc] theorem coefficientShearRootStrictPositiveOppositeCoordinates_terminalFirst :
    (PolygonPinching.componentι K (2 * s + 5) ⟨s + 2, by omega⟩).left ≫ PN ≫ (O).hom =
      ProjectiveLine.endpointReversal K ≫ T₁ := by
  have H := coefficientShearRootStrictPositiveOppositeCoordinates_first
    hπ data D s hs hstart hk hp t ⟨s + 1, by omega⟩
  rw [coefficientShearRootStrictPositiveBranchComponent_terminal] at H
  change _ = _ ≫ coefficientShearRootFinalTerminalComponent hπ data D s hs hk hp 1 ≫ _ at H
  rw [coefficientShearRootStrictPositiveTerminal_second_rootChange
    hπ data D s hs hstart hk hp t b hb ht hrt] at H
  exact H

/-- The second terminal position is the entire other independent companion-root component. -/
@[reassoc] theorem coefficientShearRootStrictPositiveOppositeCoordinates_terminalSecond :
    (PolygonPinching.componentι K (2 * s + 5) ⟨s + 3, by omega⟩).left ≫ PN ≫ (O).hom = T₂ := by
  have H := coefficientShearRootStrictPositiveOppositeCoordinates_second
    hπ data D s hs hstart hk hp t ⟨s + 1, by omega⟩
  rw [coefficientShearRootStrictPositiveBranchComponent_terminal] at H
  change _ = coefficientShearRootFinalTerminalComponent hπ data D s hs hk hp 0 ≫ _ at H
  rw [coefficientShearRootStrictPositiveTerminal_first_rootChange
    hπ data D s hs hstart hk hp t b hb ht hrt] at H
  simpa only [Fin.val_mk, show 2 * s + 4 - (s + 1) = s + 3 by omega] using H

end FLT.Mazur.WeierstrassDividedDepth
