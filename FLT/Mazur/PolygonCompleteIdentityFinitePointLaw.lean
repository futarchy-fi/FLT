/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LaurentPairEvaluation
public import FLT.Mazur.PolygonCompleteIdentityFiniteAlgebra
public import FLT.Mazur.PolygonCompleteIdentityFiniteUnits

/-!
# The original finite multiplication on all coefficient-algebra points

Evaluate the actual full Laurent law on arbitrary units. The resulting
operation is the original group operation, as detected by its monomorphic
finite-stage inclusion. Consequently it is associative without assuming the
still-open identification with ordinary multiplication of units.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open LaurentPolynomial LaurentUnitPoints LaurentPairEvaluation
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n) (m : ℕ)
variable (B : Type) [CommRing B] [Algebra (Ring K m) B]
local notation "A" => Ring K m
local notation "G" => completePointOriginalBaseGroup K n h i
local notation "e" => completeIdentityStageTorus K n h i m
local notation "b" => Spec.map (CommRingCat.ofHom (algebraMap (A) (A)[T;T⁻¹]))
local notation "s" => Spec.map (CommRingCat.ofHom (algebraMap (A) B)) ≫ baseToSeries K m

/-- Each unit gives its actual original identity-group point over the complete base. -/
def completeIdentityFinitePoint (u : Bˣ) : Over.mk (s) ⟶ (G).X :=
  Over.homMk (Spec.map (CommRingCat.ofHom (evalUnit (R := A) u).toRingHom) ≫ (e)) (by
    rw [Category.assoc, (completeIdentityFiniteParameter_isPullback K n h i m).w,
      ← Category.assoc, ← Spec.map_comp]
    exact congrArg (fun f : (A) →+* B ↦ Spec.map (CommRingCat.ofHom f) ≫ baseToSeries K m)
      (RingHom.ext (evalUnit_C u)))

/-- The original finite-stage inclusion distinguishes every coefficient-algebra unit. -/
theorem completeIdentityFinitePoint_injective :
    Function.Injective (completeIdentityFinitePoint K n h i m B) := by
  intro u v he
  have hf := congrArg Over.Hom.left he
  change Spec.map (CommRingCat.ofHom (evalUnit (R := A) u).toRingHom) ≫ (e) =
    Spec.map (CommRingCat.ofHom (evalUnit (R := A) v).toRingHom) ≫ (e) at hf
  have ha := congrArg CommRingCat.Hom.hom (Spec.map_injective ((cancel_mono (e)).mp hf))
  have ht := congrArg (fun f : (A)[T;T⁻¹] →+* B ↦ f (T 1)) ha
  apply Units.ext
  change evalUnit (R := A) u (T 1) = evalUnit (R := A) v (T 1) at ht
  simpa only [evalUnit_T, zpow_one] using ht

/-- Evaluate the actual original finite Laurent multiplication, retaining all nilpotents. -/
def completeIdentityFinitePointMul (u v : Bˣ) : Bˣ :=
  Units.map (pairEval (R := A) u v).toMonoidHom (completeIdentityFiniteMulUnit K n h i m)
local notation "F" => completeIdentityFinitePoint K n h i m B
local notation "M" => completeIdentityFinitePointMul K n h i m B

/-- The evaluated original coordinate law is exactly multiplication in the original group. -/
theorem completeIdentityFinitePoint_mul (u v : Bˣ) : (F) ((M) u v) = (F) u * (F) v := by
  have he : Spec.map (CommRingCat.ofHom (evalUnit (R := A) ((M) u v)).toRingHom) =
      Spec.map (CommRingCat.ofHom (pairEval (R := A) u v).toRingHom) ≫
        completeIdentityFiniteMulCoordinates K n h i m := by
    rw [← completeIdentityFiniteMulAlgebra_spec, ← Spec.map_comp]
    apply congrArg (fun f ↦ Spec.map (CommRingCat.ofHom f))
    exact (congrArg AlgHom.toRingHom
      (pairEval_law u v (completeIdentityFiniteMulAlgebra K n h i m))).symm
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (evalUnit (R := A) ((M) u v)).toRingHom) ≫ (e) = _
  rw [he, Category.assoc, completeIdentityFiniteMulCoordinates_original,
    completeIdentityFiniteOriginalMul, ← Category.assoc]
  apply congrArg (· ≫ (μ[(G).X]).left)
  apply pullback.hom_ext
  · rw [Category.assoc, completeIdentityFinitePair_fst, ← Category.assoc, ← Spec.map_comp]
    exact (congrArg (fun f : (A)[T;T⁻¹] →+* B ↦ Spec.map (CommRingCat.ofHom f) ≫ (e))
      (pairEval_first u v)).trans (congrArg Over.Hom.left
        (CartesianMonoidalCategory.lift_fst (F u) (F v))).symm
  · rw [Category.assoc, completeIdentityFinitePair_snd, ← Category.assoc, ← Spec.map_comp]
    exact (congrArg (fun f : (A)[T;T⁻¹] →+* B ↦ Spec.map (CommRingCat.ofHom f) ≫ (e))
      (pairEval_second u v)).trans (congrArg Over.Hom.left
        (CartesianMonoidalCategory.lift_snd (F u) (F v))).symm

/-- The actual finite law is associative on every coefficient algebra, including nilpotent ones. -/
theorem completeIdentityFinitePointMul_assoc (u v w : Bˣ) :
    (M) ((M) u v) w = (M) u ((M) v w) := by
  apply completeIdentityFinitePoint_injective K n h i m B
  simp only [completeIdentityFinitePoint_mul, _root_.mul_assoc]

/-- The actual finite law is commutative on every coefficient algebra. -/
theorem completeIdentityFinitePointMul_comm (u v : Bˣ) : (M) u v = (M) v u := by
  apply completeIdentityFinitePoint_injective K n h i m B
  simp only [completeIdentityFinitePoint_mul, _root_.mul_comm]

end FLT.Mazur.PolygonInfinitesimalStages
