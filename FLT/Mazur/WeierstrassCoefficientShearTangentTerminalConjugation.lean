/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearTangentRootEvaluation
public import FLT.Mazur.WeierstrassCoefficientShearRootTerminalRootChange

/-!
# Actual integral tangent conjugation on complete terminal components

The independently constructed companion-root comparison identifies the entire
projective components inside the original tangent model, including both endpoints.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type) [Field S] [Algebra R S] (r : S) (j : ℕ) (hj : j + 1 ≤ n)
variable (hs : algebraMap R S (π ^ (start + j)) = 0)
  (hp : algebraMap R S π = 0)
  (h3 : algebraMap R S (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b3 = 0)
  (h4 : algebraMap R S (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b4 = 0)
  (h6 : algebraMap R S (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
  (a : Sˣ) (ha : (a : S) = (rootShearCurve (W.map (algebraMap R S)) r).a₁)
variable (t : S)
  (ht : t ^ 2 + algebraMap R S W.a₁ * t - algebraMap R S W.a₂ = 0)
  (b : Sˣ) (hb : (b : S) = (rootShearCurve (W.map (algebraMap R S)) t).a₁)
  (hrt : r + t = -algebraMap R S W.a₁)
include hrt

local notation "Mr" => coefficientShearTangentRootSpecialization
  hπ data S r hr (j + 1) hj
local notation "Mt" => coefficientShearTangentRootSpecialization
  hπ data S t ht (j + 1) hj
local notation "σ" => coefficientShearTangentConjugation hπ data (j + 1) hj

/-- The complete first terminal component exchanges under actual integral conjugation. -/
@[reassoc] theorem coefficientShearTangentTerminalFirstComponent_conjugation :
    coefficientShearRootTerminalFirstComponent
        hπ data S r j hj hs hp h3 h4 h6 hr a ha ≫ Mr ≫ σ =
      coefficientShearRootTerminalSecondComponent
        hπ data S t j hj hs hp h3 h4 h6 ht b hb ≫ Mt := by
  rw [coefficientShearTangentRootSpecialization_conjugation
    hπ data S r hr (j + 1) hj t ht hrt,
    ← Category.assoc, coefficientShearRootTerminalFirstComponent_rootChange
      hπ data S r j hj hs hp h3 h4 h6 hr a ha t ht b hb hrt]

/-- The complete second terminal component exchanges under actual integral conjugation. -/
@[reassoc] theorem coefficientShearTangentTerminalSecondComponent_conjugation :
    coefficientShearRootTerminalSecondComponent
        hπ data S r j hj hs hp h3 h4 h6 hr a ha ≫ Mr ≫ σ =
      coefficientShearRootTerminalFirstComponent
        hπ data S t j hj hs hp h3 h4 h6 ht b hb ≫ Mt := by
  rw [coefficientShearTangentRootSpecialization_conjugation
    hπ data S r hr (j + 1) hj t ht hrt,
    ← Category.assoc, coefficientShearRootTerminalSecondComponent_rootChange
      hπ data S r j hj hs hp h3 h4 h6 hr a ha t ht b hb hrt]

end FLT.Mazur.WeierstrassDividedDepth
