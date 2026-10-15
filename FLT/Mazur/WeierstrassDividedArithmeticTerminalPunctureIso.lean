/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticTerminalPunctureImages
public import FLT.Mazur.WeierstrassDividedArithmeticTerminalNodeOpen

/-!
# Full original terminal Laurent boundaries are the standard node punctures

The isomorphism is between the entire Laurent scheme and the actual
localization D(p) or D(q). Its composite is the original normalized boundary.
-/

@[expose] public noncomputable section
open Polynomial AlgebraicGeometry CategoryTheory
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages WeierstrassSuccessiveX
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
variable {R : Type} [CommRing R]
  {W : WeierstrassCurve R} {π : R} {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (m : ℕ)
local notation "Q" => Quotient R π m
local notation "q" => algebraMap R Q

variable (j : ℕ) (hj : j + 1 ≤ n)
local notation "d" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "x" => WeierstrassDilatation.x W (π ^ (start + j + 1))
  (Data.b3 d) (Data.b4 d) (Data.b6 d)
local notation "t" => coord W (π ^ (start + j)) π (Data.b3 d) (Data.b4 d) (Data.b6 d) 0
local notation "a" => depthOverlapEquiv W π (start + j) (Data.b3 d) (Data.b4 d) (Data.b6 d)

variable (ha : IsUnit W.a₁) (hs : π ∣ π ^ (start + j)) (h2 : π ∣ W.a₂)
  (h3 : π ∣ (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b3)
  (h4 : π ∣ (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b4)
  (h6 : π ∣ (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6) (opposite : Bool)
local notation "s" => π ^ (start + j + 1)
local notation "U" => W.map q
local notation "J" => ideal Q (parameter R π m)
local notation "hJ" => arithmeticParameterIdeal_nilpotent π m
local notation "hs₂" => dvd_pow_self π (Nat.succ_ne_zero (start + j))
local notation "r" => WeierstrassDilatation.terminalTangentRoot U (q s) J hJ (ha.map q)
  (arithmeticCoefficient_mem π m hs₂) (arithmeticCoefficient_mem π m h2)
local notation "hrI" => WeierstrassDilatation.terminalTangentRoot_mem U (q s) J hJ (ha.map q)
  (arithmeticCoefficient_mem π m hs₂) (arithmeticCoefficient_mem π m h2)
local notation "hr" => WeierstrassDilatation.terminalTangentRoot_equation U (q s) J hJ (ha.map q)
  (arithmeticCoefficient_mem π m hs₂) (arithmeticCoefficient_mem π m h2)
local notation "h4₀" => arithmeticCoefficient_mem π m h4
local notation "h6₀" => arithmeticCoefficient_mem π m h6
local notation "v" => arithmeticBranchSlope π m W (π ^ (start + j))
  (Data.b3 d) (Data.b4 d) (Data.b6 d) ha hs h2 h3 h4 h6 opposite
local notation "hv" => arithmeticBranchSlope_equation π m W (π ^ (start + j))
  (Data.b3 d) (Data.b4 d) (Data.b6 d) ha hs h2 h3 h4 h6 opposite
local notation "G" => tensorTerminalLaurent W π (start + j)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) Q v hv
local notation "c" => WeierstrassDilatation.arithmeticTerminalSmoothing π m W s
  (Data.b3 d) (Data.b4 d) (Data.b6 d) ha hs₂ h2 h4 h6
local notation "e" => WeierstrassDilatation.arithmeticTerminalNodeIso π m W s
  (Data.b3 d) (Data.b4 d) (Data.b6 d) ha hs₂ h2 h4 h6

local notation "E" => terminalArithmeticNodeEvaluation data m j hj ha hs h2 h3 h4 h6
local notation "δ" => ite (opposite = true) (NodalFiber.p c) (NodalFiber.q c)

local notation "B" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom (E opposite)))
local notation "L" => Localization.Away δ
local notation "i" => Spec.map (CommRingCat.ofHom (algebraMap (NodalFiber.Coordinate c) L))

/-- Identify the entire original labeled Laurent boundary with its full standard puncture. -/
def terminalArithmeticPunctureIso : Spec (.of Q[T;T⁻¹]) ≅ Spec (.of L) := by
  let _ := terminalArithmeticNodeEvaluation_isOpenImmersion
    data m j hj ha hs h2 h3 h4 h6 opposite
  let _ : IsOpenImmersion i := IsOpenImmersion.of_isLocalization δ
  apply IsOpenImmersion.isoOfRangeEq B i
  exact (terminalArithmeticNodeEvaluation_range data m j hj ha hs h2 h3 h4 h6 opposite).trans
    (PrimeSpectrum.localization_away_comap_range L δ).symm

/-- The puncture comparison preserves the full original normalized boundary morphism. -/
@[reassoc] theorem terminalArithmeticPunctureIso_boundary :
    (terminalArithmeticPunctureIso data m j hj ha hs h2 h3 h4 h6 opposite).hom ≫ i = B := by
  let _ := terminalArithmeticNodeEvaluation_isOpenImmersion
    data m j hj ha hs h2 h3 h4 h6 opposite
  let _ : IsOpenImmersion i := IsOpenImmersion.of_isLocalization δ
  exact IsOpenImmersion.isoOfRangeEq_hom_fac B i
    ((terminalArithmeticNodeEvaluation_range data m j hj ha hs h2 h3 h4 h6 opposite).trans
      (PrimeSpectrum.localization_away_comap_range L δ).symm)

/-- The inverse comparison retains the actual full Laurent parameterization. -/
@[reassoc] theorem terminalArithmeticPunctureIso_inv_boundary :
    (terminalArithmeticPunctureIso data m j hj ha hs h2 h3 h4 h6 opposite).inv ≫ B = i := by
  let _ := terminalArithmeticNodeEvaluation_isOpenImmersion
    data m j hj ha hs h2 h3 h4 h6 opposite
  let _ : IsOpenImmersion i := IsOpenImmersion.of_isLocalization δ
  exact IsOpenImmersion.isoOfRangeEq_inv_fac B i
    ((terminalArithmeticNodeEvaluation_range data m j hj ha hs h2 h3 h4 h6 opposite).trans
      (PrimeSpectrum.localization_away_comap_range L δ).symm)

/-- The complete puncture isomorphism commutes with the original quotient coefficient map. -/
@[reassoc] theorem terminalArithmeticPunctureIso_structure :
    (terminalArithmeticPunctureIso data m j hj ha hs h2 h3 h4 h6 opposite).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap Q L)) =
        Spec.map (CommRingCat.ofHom (algebraMap Q Q[T;T⁻¹])) := by
  have hi : i ≫ Spec.map (CommRingCat.ofHom (algebraMap Q (NodalFiber.Coordinate c))) =
      Spec.map (CommRingCat.ofHom (algebraMap Q L)) := by
    rw [← Spec.map_comp]
    rfl
  rw [← hi, ← Category.assoc, terminalArithmeticPunctureIso_boundary,
    ← Spec.map_comp]
  exact congrArg (fun f : Q →+* Q[T;T⁻¹] ↦ Spec.map (CommRingCat.ofHom f))
    (E opposite).comp_algebraMap

end FLT.Mazur.WeierstrassDividedDepth
