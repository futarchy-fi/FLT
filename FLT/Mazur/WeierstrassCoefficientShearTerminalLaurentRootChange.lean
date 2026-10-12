/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearRootLaurentOverlap
public import FLT.Mazur.WeierstrassSuccessiveShearTerminalLaurentRootChange
public import FLT.Mazur.WeierstrassCoefficientShearRootChange

/-!
# Root exchange on the full Laurent chart of the actual coefficient model

Reconstruction through the actual original tensor chart identifies opposite
Laurent charts with their actual scaled reciprocal parameters.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [Field S] [Algebra R S] (r : S) (j : ℕ) (hj : j + 1 ≤ n)
local notation "d" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
variable (hp : algebraMap R S π = 0)
  (h3 : algebraMap R S (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b3 = 0)
  (h4 : algebraMap R S (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b4 = 0)
  (hc : IsUnit (algebraMap R S (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6))
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
  (a : Sˣ) (ha : (a : S) = (rootShearCurve (W.map (algebraMap R S)) r).a₁)
local notation "hsNext" => show algebraMap R S (π ^ (start + (j + 1))) = 0 from by
  rw [← Nat.add_assoc, pow_succ, map_mul, hp, mul_zero]
variable (t : S)
  (ht : t ^ 2 + algebraMap R S W.a₁ * t - algebraMap R S W.a₂ = 0)
  (b : Sˣ) (hb : (b : S) = (rootShearCurve (W.map (algebraMap R S)) t).a₁)
  (hrt : r + t = -algebraMap R S W.a₁)
local notation "C" => coefficientShearRootChange hπ data S r t (j + 1) hj
local notation "G" => coefficientShearGluedIso hπ data S t (j + 1) hj
include hrt

local notation "q" => Spec.map
  (CommRingCat.ofHom (PolygonScaledReciprocal.reciprocal hc.unit).toRingHom)

/-- Root exchange retains the full terminal torus and its divided-constant scale. -/
@[reassoc] theorem coefficientShearRootChange_terminalLaurent :
    coefficientShearTerminalLaurent hπ data S r (j + 1) hj
        hsNext h3 h4 hc hr a ha ≫ (C).hom =
      q ≫ coefficientShearTerminalLaurent hπ data S t (j + 1) hj
        hsNext h3 h4 hc ht b hb := by
  apply (cancel_mono (G).hom).mp
  rw [Category.assoc, coefficientShearRootChange_reconstruction, Category.assoc,
    coefficientShearRootTerminalLaurent_reconstruction (hp := hp),
    coefficientShearRootTerminalLaurent_reconstruction (hp := hp), ← Category.assoc]
  apply congrArg (· ≫ globalDividedTensorChart hπ data S (j + 1) hj)
  change Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp]
  rw [tensorShearTerminalLaurentEquiv_rootChange W π (start + j)
    (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hp h3 h4 hr hc a ha t ht b hb hrt]
  rfl

end FLT.Mazur.WeierstrassDividedDepth
