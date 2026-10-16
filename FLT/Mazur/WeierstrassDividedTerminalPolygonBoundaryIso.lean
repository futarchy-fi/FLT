/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTerminalPolygonBoundary
public import FLT.Mazur.WeierstrassDividedArithmeticTerminalPunctureIso
public import FLT.Mazur.NodalFiberUnitScalingPunctureRange

/-!
# Invertibility of the actual terminal boundary parameters

The full original puncture and the normalized polygon puncture have the same
range. Cancellation identifies their isomorphism with the actual Laurent map.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages WeierstrassDilatation
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R]
  {W : WeierstrassCurve R} {π : R} {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (m : ℕ)
  (j : ℕ) (hj : j + 1 ≤ n)
local notation "d" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
variable (ha : IsUnit W.a₁) (hs : π ∣ π ^ (start + j)) (h2 : π ∣ W.a₂)
  (h3 : π ∣ (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b3)
  (h4 : π ∣ (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b4)
  (h6 : π ∣ (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6)
  (u : Rˣ) (hprimitive : Data.b6 (data ⟨j + 1, Nat.lt_succ_of_le hj⟩) = π * ↑u)
include hprimitive
local notation "Q" => Quotient R π m
local notation "s" => π ^ (start + j + 1)
local notation "hs₂" => dvd_pow_self π (Nat.succ_ne_zero (start + j))
local notation "c" => arithmeticTerminalSmoothing π m W s
  (Data.b3 d) (Data.b4 d) (Data.b6 d) ha hs₂ h2 h4 h6
local notation "v" => arithmeticCoherentTerminalUnit π W s
  (Data.b3 d) (Data.b4 d) (Data.b6 d) ha hs₂ h2 h3 h4 h6 u hprimitive m
local notation "E" => terminalArithmeticNodeEvaluation data m j hj ha hs h2 h3 h4 h6
local notation "P" => coherentTerminalPolygonIso π W s
  (Data.b3 d) (Data.b4 d) (Data.b6 d) ha hs₂ h2 h3 h4 h6 u hprimitive m

/-- The normalized full terminal boundary has the corresponding standard puncture range. -/
theorem terminalPolygonBoundary_range (opposite : Bool) :
    Set.range (Spec.map (CommRingCat.ofHom (E opposite).toRingHom) ≫ (P).hom) =
      Set.range (if opposite then PolygonSmoothing.leftBranchOpen Q (parameter R π m)
        else PolygonSmoothing.rightBranchOpen Q (parameter R π m)) :=
  NodalFiber.unitSmoothingIso_comp_range c (parameter R π m) v
    (arithmeticCoherentTerminalUnit_spec π W s (Data.b3 d) (Data.b4 d) (Data.b6 d)
      ha hs₂ h2 h3 h4 h6 u hprimitive m) _ opposite
    (terminalArithmeticNodeEvaluation_range data m j hj ha hs h2 h3 h4 h6 opposite)

/-- Each exact corrected Laurent parameter is an isomorphism on the entire torus. -/
instance terminalPolygonBoundaryParameter_isIso (opposite : Bool) :
    IsIso (terminalPolygonBoundaryParameter data m j hj
      ha hs h2 h3 h4 h6 u hprimitive opposite) := by
  let f := Spec.map (CommRingCat.ofHom (E opposite).toRingHom) ≫ (P).hom
  let b := if opposite then PolygonSmoothing.leftBranchOpen Q (parameter R π m)
    else PolygonSmoothing.rightBranchOpen Q (parameter R π m)
  let _ := terminalArithmeticNodeEvaluation_isOpenImmersion
    data m j hj ha hs h2 h3 h4 h6 opposite
  let _ : IsOpenImmersion f := IsOpenImmersion.comp _ _
  let _ : IsOpenImmersion b := by cases opposite <;> dsimp [b] <;> infer_instance
  have hr : Set.range f = Set.range b := by
    cases opposite <;>
      exact terminalPolygonBoundary_range data m j hj ha hs h2 h3 h4 h6 u hprimitive _
  let e := IsOpenImmersion.isoOfRangeEq f b hr
  have he : terminalPolygonBoundaryParameter data m j hj
      ha hs h2 h3 h4 h6 u hprimitive opposite = e.hom := by
    apply (cancel_mono b).mp
    exact (terminalPolygon_boundary data m j hj ha hs h2 h3 h4 h6 u hprimitive opposite).symm.trans
      (IsOpenImmersion.isoOfRangeEq_hom_fac f b _).symm
  rw [he]
  infer_instance

/-- The full original-to-polygon Laurent change, packaged with its constructed inverse. -/
def terminalPolygonBoundaryIso (opposite : Bool) :
    PolygonSmoothing.branchTorus Q ≅ PolygonSmoothing.branchTorus Q :=
  asIso (terminalPolygonBoundaryParameter data m j hj ha hs h2 h3 h4 h6 u hprimitive opposite)

/-- Reparameterizing by the inverse recovers the exact standard full boundary. -/
@[reassoc] theorem terminalPolygonBoundaryIso_inv_boundary (opposite : Bool) :
    (terminalPolygonBoundaryIso data m j hj ha hs h2 h3 h4 h6 u hprimitive opposite).inv ≫
      Spec.map (CommRingCat.ofHom (E opposite).toRingHom) ≫ (P).hom =
    (if opposite then PolygonSmoothing.leftBranchOpen Q (parameter R π m)
      else PolygonSmoothing.rightBranchOpen Q (parameter R π m)) := by
  rw [terminalPolygon_boundary]
  exact (terminalPolygonBoundaryIso data m j hj
    ha hs h2 h3 h4 h6 u hprimitive opposite).inv_hom_id_assoc _

end FLT.Mazur.WeierstrassDividedDepth
