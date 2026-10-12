/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveShearComponents

/-!
# Coefficient specialization of the original retained line functions

The original three coordinates restrict to zero, the unsheared slope and the
free polynomial parameter. These entire line maps commute with coefficient change.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.WeierstrassSuccessiveX
open WeierstrassDividedDepth WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (s π b3 b4 b6 : R)
  (S : Type u) [CommRing S] [Algebra R S] (r : S)
  (hs : algebraMap R S s = 0) (hp : algebraMap R S π = 0)
  (h3 : algebraMap R S b3 = 0) (h4 : algebraMap R S b4 = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
  (v : S) (hv : v * (v + (rootShearCurve (W.map (algebraMap R S)) r).a₁) = 0)
local notation "LS" => tensorShearLineMap W s π b3 b4 b6 S r hs hp h3 h4 hr v hv

/-- Restrict the actual original integral chart functions to a retained line. -/
def originalShearLineMap : Coordinate W s π b3 b4 b6 →ₐ[R] S[X] :=
  ((LS).restrictScalars R).comp Algebra.TensorProduct.includeRight

/-- All three original functions retain their explicit unsheared line values. -/
@[simp] theorem originalShearLineMap_coord (i : Fin 3) :
    originalShearLineMap W s π b3 b4 b6 S r hs hp h3 h4 hr v hv
      (coord W s π b3 b4 b6 i) = ![0, C (v + r), X] i :=
  tensorShearLineMap_coord W s π b3 b4 b6 S r hs hp h3 h4 hr v hv i

open AlgebraicGeometry CategoryTheory in
/-- The original line restriction is the composite of the actual tensor and integral maps. -/
theorem originalShearLineMap_spec :
    Spec.map (CommRingCat.ofHom (LS).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
          Coordinate W s π b3 b4 b6 →ₐ[R] ScalarExtension W s π b3 b4 b6 S).toRingHom) =
      Spec.map (CommRingCat.ofHom
        (originalShearLineMap W s π b3 b4 b6 S r hs hp h3 h4 hr v hv).toRingHom) := by
  rw [← Spec.map_comp]
  rfl

variable (T : Type u) [CommRing T] [Algebra R T] (f : S →ₐ[R] T) (t w : T)
  (gs : algebraMap R T s = 0) (gp : algebraMap R T π = 0)
  (g3 : algebraMap R T b3 = 0) (g4 : algebraMap R T b4 = 0)
  (ht : t ^ 2 + algebraMap R T W.a₁ * t - algebraMap R T W.a₂ = 0)
  (hw : w * (w + (rootShearCurve (W.map (algebraMap R T)) t).a₁) = 0)

/-- An actual coefficient map preserves the whole line whenever it preserves the original slope. -/
theorem originalShearLineMap_coefficient (hvw : f (v + r) = w + t) :
    (Polynomial.mapAlgHom f).comp
        (originalShearLineMap W s π b3 b4 b6 S r hs hp h3 h4 hr v hv) =
      originalShearLineMap W s π b3 b4 b6 T t gs gp g3 g4 ht w hw := by
  apply hom_ext
  intro i
  simp only [AlgHom.comp_apply, originalShearLineMap_coord]
  fin_cases i
  · exact map_zero _
  · change Polynomial.map f.toRingHom (C (v + r)) = C (w + t)
    rw [Polynomial.map_C]
    exact congrArg C hvw
  · exact Polynomial.map_X f.toRingHom

end FLT.Mazur.WeierstrassSuccessiveX
