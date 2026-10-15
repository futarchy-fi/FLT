/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticTerminalPunctureUnits
public import FLT.Mazur.WeierstrassDividedArithmeticTerminalPunctureCoverage

/-!
# Exact images of the original normalized terminal Laurent boundaries

The small Boolean label has image the complete D(q), and the opposite label
has image the complete D(p). The nilpotent coordinate excludes the wrong label.
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

/-- The actual labeled Laurent boundary has exactly its complete standard puncture as image. -/
theorem terminalArithmeticNodeEvaluation_range :
    Set.range (Spec.map (CommRingCat.ofHom (E opposite).toRingHom)) =
      (PrimeSpectrum.basicOpen δ : Set (PrimeSpectrum (NodalFiber.Coordinate c))) := by
  ext z
  change (∃ y, Spec.map (CommRingCat.ofHom (E opposite).toRingHom) y = z) ↔ δ ∉ z.asIdeal
  constructor
  · rintro ⟨y, rfl⟩
    exact y.asIdeal.notMem_of_isUnit
      (terminalArithmeticSelected_unit data m j hj ha hs h2 h3 h4 h6 opposite)
  · intro hz
    obtain ⟨label, y, hy⟩ := terminalArithmeticPuncture_covered
      data m j hj ha hs h2 h3 h4 h6 opposite z hz
    have hl : label = opposite := by
      by_contra hne
      have he : δ = (if label then NodalFiber.q c else NodalFiber.p c) := by
        cases label <;> cases opposite
        · exact False.elim (hne rfl)
        · rfl
        · rfl
        · exact False.elim (hne rfl)
      have hn : IsNilpotent (E label δ) := by
        rw [he]
        exact terminalArithmeticUnselected_nilpotent data m j hj ha hs h2 h3 h4 h6 label
      apply hz
      rw [← hy]
      exact nilpotent_iff_mem_prime.mp hn y.asIdeal inferInstance
    exact ⟨y, hl ▸ hy⟩

/-- Distinct original Boolean labels have disjoint full terminal boundary images. -/
theorem terminalArithmeticNodeEvaluation_disjoint :
    Disjoint (Set.range (Spec.map (CommRingCat.ofHom (E false).toRingHom)))
      (Set.range (Spec.map (CommRingCat.ofHom (E true).toRingHom))) := by
  rw [Set.disjoint_left]
  rintro z ⟨y, rfl⟩ hz
  rw [terminalArithmeticNodeEvaluation_range data m j hj ha hs h2 h3 h4 h6 true] at hz
  change NodalFiber.p c ∉ _ at hz
  exact hz (nilpotent_iff_mem_prime.mp
    (terminalArithmeticUnselected_nilpotent data m j hj ha hs h2 h3 h4 h6 false)
      y.asIdeal inferInstance)

end FLT.Mazur.WeierstrassDividedDepth
