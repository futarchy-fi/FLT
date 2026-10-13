/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearScaleOneEqualityParameters
import all FLT.Mazur.WeierstrassCoefficientShearRetainedFiber

import all FLT.Mazur.WeierstrassCoefficientShearScaleOneEqualityParameters

/-!
# The full conic and divided equation cover the scale-one equality component

Extract the entire conic and divided equation, including both incidence markings.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
open scoped Polynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX WeierstrassModificationX WeierstrassDilatation
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {R : Type u} [CommRing R]
  {W : WeierstrassCurve R} {π : R} {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [Field S] [Algebra R S] (r : S) (j : ℕ) (hj : j + 1 ≤ n)
local notation "d" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
variable (hp : algebraMap R S π = 0)
  (h3 : algebraMap R S (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b3 = 0)
  (h4 : algebraMap R S (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b4 = 0)
  (hc : IsUnit (algebraMap R S (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6))
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
  (a : Sˣ) (ha : (a : S) = (rootShearCurve (W.map (algebraMap R S)) r).a₁)
local notation "U" => rootShearCurve (W.map (algebraMap R S)) r
local notation "c" => algebraMap R S (Data.b6 d)
local notation "hu" => Eq.mp (congrArg IsUnit ha) (Units.isUnit a)
local notation "hsNext" => show algebraMap R S (π ^ (start + (j + 1))) = 0 from by
  rw [← Nat.add_assoc, pow_succ, map_mul, hp, mul_zero]
local notation "hsAux" => show algebraMap R S (π ^ (start + j + 1)) = 0 from by
  rw [pow_succ, map_mul, hp, mul_zero]
local notation "P" => WeierstrassSuccessiveShearTerminal.laurentConicComponent
  W π (start + j + 1) (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hsAux hp h3 h4 hr hc a ha
local notation "l" => WeierstrassSuccessiveShearTerminal.laurentConicComponentConic
  W π (start + j + 1) (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hsAux hp h3 h4 hr hc a ha
local notation "t" => WeierstrassSuccessiveShearTerminal.laurentConicComponentTorus
  W π (start + j + 1) (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hsAux hp h3 h4 hr hc a ha
local notation "p" => WeierstrassSuccessiveShearTerminal.laurentConicComponentStructure
  W π (start + j + 1) (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hsAux hp h3 h4 hr hc a ha
local notation "J" => WeierstrassSuccessiveShearTerminal.laurentConicComponentProjectiveIso
  W π (start + j + 1) (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hsAux hp h3 h4 hr hc a ha
local notation "q" => coefficientShearScaleOneEqualityConicParameter
  data S r j hj hp h3 h4 hc hr a ha

local notation "e" => coefficientShearLaurentEquiv W (π ^ (start + (j + 1)))
  (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hsNext h3 h4 hr a ha hc
local notation "E" => Scheme.Spec.mapIso (e).toRingEquiv.toCommRingCatIso.op
local notation "v" => coefficientShearEqualityDividedParameter
  data S r j hj hp h3 h4 hc hr a ha

/-- The full original conic and divided parameters jointly detect arbitrary target maps. -/
theorem coefficientShearScaleOneEqualityParameters_hom_ext {Y : Scheme.{u}}
    (f g : ProjectiveLine.scheme S ⟶ Y)
    (hq : q ≫ f = q ≫ g) (hv : v ≫ f = v ≫ g) : f = g := by
  apply (cancel_epi (J).inv).mp
  apply pushout.hom_ext
  · change l ≫ (J).inv ≫ f = l ≫ (J).inv ≫ g
    simpa only [coefficientShearScaleOneEqualityConicParameter, Category.assoc] using hq
  · change t ≫ (J).inv ≫ f = t ≫ (J).inv ≫ g
    have ht : t ≫ (J).inv = ProjectiveLine.overlapLeft S ≫ ProjectiveLine.left S := by
      rw [← WeierstrassSuccessiveShearTerminal.laurentConicComponentProjectiveIso_torus,
        Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    have H := congrArg (fun m => (E).hom ≫ m) hv
    rw [coefficientShearEqualityDividedParameter_laurent_assoc,
      coefficientShearEqualityDividedParameter_laurent_assoc] at H
    simpa only [← Category.assoc, ht] using H

end FLT.Mazur.WeierstrassDividedDepth
