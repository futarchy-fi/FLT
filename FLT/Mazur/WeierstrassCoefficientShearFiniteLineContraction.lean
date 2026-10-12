/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveShearComponents
public import FLT.Mazur.WeierstrassDividedDepthData
public import FLT.Mazur.WeierstrassDilatationResidueRetained

/-!
# Coefficient-split lines over the actual preceding divided tensor chart

Transport the original preceding contraction through its parameter equality
over the chosen coefficient algebra. The line parameter stays the
original horizontal coordinate; neither tangent orientation is changed.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {k : ℕ}
  (d : Data W π k) (e : Data W π (k + 1))
  (S : Type u) [CommRing S] [Algebra R S] (r : S)
  (hs : algebraMap R S (π ^ k) = 0) (hp : algebraMap R S π = 0)
  (h3 : algebraMap R S e.b3 = 0) (h4 : algebraMap R S e.b4 = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
open WeierstrassSuccessiveX
local notation "A" => WeierstrassDilatation.Coordinate W (π ^ k)
  (Data.b3 d) (Data.b4 d) (Data.b6 d)
local notation "T" => WeierstrassDilatation.ScalarExtension W (π ^ k)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) S
local notation "p" => WeierstrassDilatation.parameterEquiv W (π ^ k)
  (π ^ k) (Data.b3 d) (Data.b4 d) (Data.b6 d)
  (π * Data.b3 e) (π * Data.b4 e) (π ^ 2 * Data.b6 e) rfl
  (factor3_step hπ d e) (factor4_step hπ d e) (factor6_step hπ d e)
local notation "f" => tensorPreviousMap W (π ^ k) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e) S
local notation "tx" => WeierstrassDilatation.tensorX W (π ^ k)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) S
local notation "ty" => WeierstrassDilatation.tensorY W (π ^ k)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) S
variable (v : S) (hv : v * (v + (rootShearCurve (W.map (algebraMap R S)) r).a₁) = 0)
local notation "L" => tensorShearLineMap W (π ^ k) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e) S r hs hp h3 h4 hr v hv

/-- Restriction to an actual horizontal line after the preceding parameter transport. -/
def coefficientShearFiniteLineContraction : A →ₐ[R] S[X] :=
  (AlgHom.restrictScalars R L).comp ((f).comp (AlgEquiv.toAlgHom p))

/-- The same full contraction on the actual preceding tensor algebra. -/
def tensorShearFiniteLineContraction : T →ₐ[S] S[X] :=
  AlgHom.liftEquiv R S _ _ (coefficientShearFiniteLineContraction hπ d e S r hs hp h3 h4 hr v hv)

/-- The tensor horizontal coordinate remains the original line parameter. -/
theorem tensorShearFiniteLineContraction_x :
    tensorShearFiniteLineContraction hπ d e S r hs hp h3 h4 hr v hv tx = X := by
  change (1 : S) • L (f (p _)) = _
  rw [one_smul]
  rw [WeierstrassDilatation.parameterEquiv_x]
  exact tensorShearLineMap_previous_x W (π ^ k) π e.b3 e.b4 e.b6
    S r hs hp h3 h4 hr v hv

/-- The tensor vertical coordinate retains the specified original tangent slope. -/
theorem tensorShearFiniteLineContraction_y :
    tensorShearFiniteLineContraction hπ d e S r hs hp h3 h4 hr v hv ty = X * C (v + r) := by
  change (1 : S) • L (f (p _)) = _
  rw [one_smul]
  rw [WeierstrassDilatation.parameterEquiv_y]
  exact tensorShearLineMap_previous_y W (π ^ k) π e.b3 e.b4 e.b6
    S r hs hp h3 h4 hr v hv

end FLT.Mazur.WeierstrassDividedDepth
