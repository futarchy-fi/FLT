/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearTangentRootEvaluation
public import FLT.Mazur.WeierstrassCoefficientShearRootInitialRootChange

/-!
# Actual integral tangent conjugation on complete initial components

The independently constructed companion-root comparison identifies the entire
projective components inside the original tangent model, including both endpoints.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type) [Field S] [Algebra R S] (r : S)
  (h1 : 1 ≤ n) (m : ℕ) (hm : 1 + m ≤ n)
variable (hs : algebraMap R S (π ^ start) = 0) (hp : algebraMap R S π = 0)
  (h3 : algebraMap R S (data ⟨1, Nat.lt_succ_of_le h1⟩).b3 = 0)
  (h4 : algebraMap R S (data ⟨1, Nat.lt_succ_of_le h1⟩).b4 = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
  (g3 : algebraMap R S (data ⟨0, Nat.zero_lt_succ n⟩).b3 = 0)
  (g4 : algebraMap R S (data ⟨0, Nat.zero_lt_succ n⟩).b4 = 0)
  (g6 : algebraMap R S (data ⟨0, Nat.zero_lt_succ n⟩).b6 = 0)
  (a : Sˣ) (ha : (a : S) = (rootShearCurve (W.map (algebraMap R S)) r).a₁)
variable (t : S) (b : Sˣ)
  (hb : (b : S) = (rootShearCurve (W.map (algebraMap R S)) t).a₁)
  (ht : t ^ 2 + algebraMap R S W.a₁ * t - algebraMap R S W.a₂ = 0)
  (hrt : r + t = -algebraMap R S W.a₁)
include hrt

local notation "Mr" => coefficientShearTangentRootSpecialization
  hπ data S r hr (1 + m) hm
local notation "Mt" => coefficientShearTangentRootSpecialization
  hπ data S t ht (1 + m) hm
local notation "σ" => coefficientShearTangentConjugation hπ data (1 + m) hm

/-- The complete first initial component exchanges under actual integral conjugation. -/
@[reassoc] theorem coefficientShearTangentInitialFirstComponent_conjugation :
    coefficientShearRootInitialFirstComponent
        hπ data S r h1 m hm hs hp h3 h4 hr g3 g4 g6 a ha ≫ Mr ≫ σ =
      coefficientShearRootInitialSecondComponent
        hπ data S t h1 m hm hs hp h3 h4 ht g3 g4 g6 b hb ≫ Mt := by
  rw [coefficientShearTangentRootSpecialization_conjugation
    hπ data S r hr (1 + m) hm t ht hrt,
    ← Category.assoc, coefficientShearRootInitialFirstComponent_rootChange
      hπ data S r h1 m hm hs hp h3 h4 hr g3 g4 g6 a ha t b hb ht hrt]

/-- The complete second initial component exchanges under actual integral conjugation. -/
@[reassoc] theorem coefficientShearTangentInitialSecondComponent_conjugation :
    coefficientShearRootInitialSecondComponent
        hπ data S r h1 m hm hs hp h3 h4 hr g3 g4 g6 a ha ≫ Mr ≫ σ =
      coefficientShearRootInitialFirstComponent
        hπ data S t h1 m hm hs hp h3 h4 ht g3 g4 g6 b hb ≫ Mt := by
  rw [coefficientShearTangentRootSpecialization_conjugation
    hπ data S r hr (1 + m) hm t ht hrt,
    ← Category.assoc, coefficientShearRootInitialSecondComponent_rootChange
      hπ data S r h1 m hm hs hp h3 h4 hr g3 g4 g6 a ha t b hb ht hrt]

end FLT.Mazur.WeierstrassDividedDepth
