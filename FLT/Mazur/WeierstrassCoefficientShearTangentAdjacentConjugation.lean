/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearTangentRootEvaluation
public import FLT.Mazur.WeierstrassCoefficientShearAdjacentComponentRootChange

/-!
# Actual integral tangent conjugation on complete adjacent components

The independently constructed companion-root comparison identifies the entire
projective components inside the original tangent model, including both endpoints.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type) [Field S] [Algebra R S] (r : S)
  (j : ℕ) (hj : j + 1 ≤ n) (hjNext : j + 2 ≤ n)
  (m : ℕ) (hm : j + 2 + m ≤ n)
include hj hjNext
variable (hs : algebraMap R S (π ^ (start + j)) = 0) (hp : algebraMap R S π = 0)
  (h3 : algebraMap R S (Data.b3 (data ⟨j + 2, Nat.lt_succ_of_le hjNext⟩)) = 0)
  (h4 : algebraMap R S (Data.b4 (data ⟨j + 2, Nat.lt_succ_of_le hjNext⟩)) = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
include h3 h4
variable (a : Sˣ) (ha : (a : S) = (rootShearCurve (W.map (algebraMap R S)) r).a₁)
variable (t : S) (b : Sˣ)
  (hb : (b : S) = (rootShearCurve (W.map (algebraMap R S)) t).a₁)
  (ht : t ^ 2 + algebraMap R S W.a₁ * t - algebraMap R S W.a₂ = 0)
  (hrt : r + t = -algebraMap R S W.a₁)
include hrt

local notation "Mr" => coefficientShearTangentRootSpecialization
  hπ data S r hr (j + 2 + m) hm
local notation "Mt" => coefficientShearTangentRootSpecialization
  hπ data S t ht (j + 2 + m) hm
local notation "σ" => coefficientShearTangentConjugation hπ data (j + 2 + m) hm

/-- The complete first retained component exchanges under actual integral conjugation. -/
@[reassoc] theorem coefficientShearTangentAdjacentFirstComponent_conjugation :
    coefficientShearAdjacentFirstComponent
        hπ data S r j hj hjNext m hm hs hp h3 h4 hr a ha ≫ Mr ≫ σ =
      coefficientShearAdjacentSecondComponent
        hπ data S t j hj hjNext m hm hs hp h3 h4 ht b hb ≫ Mt := by
  rw [coefficientShearTangentRootSpecialization_conjugation
    hπ data S r hr (j + 2 + m) hm t ht hrt,
    ← Category.assoc, coefficientShearAdjacentFirstComponent_rootChange
      hπ data S r j hj hjNext m hm hs hp h3 h4 hr a ha t b hb ht hrt]

/-- The complete second retained component exchanges under actual integral conjugation. -/
@[reassoc] theorem coefficientShearTangentAdjacentSecondComponent_conjugation :
    coefficientShearAdjacentSecondComponent
        hπ data S r j hj hjNext m hm hs hp h3 h4 hr a ha ≫ Mr ≫ σ =
      coefficientShearAdjacentFirstComponent
        hπ data S t j hj hjNext m hm hs hp h3 h4 ht b hb ≫ Mt := by
  rw [coefficientShearTangentRootSpecialization_conjugation
    hπ data S r hr (j + 2 + m) hm t ht hrt,
    ← Category.assoc, coefficientShearAdjacentSecondComponent_rootChange
      hπ data S r j hj hjNext m hm hs hp h3 h4 hr a ha t b hb ht hrt]

end FLT.Mazur.WeierstrassDividedDepth
