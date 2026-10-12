/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveShearScaleOneConicBoundary
public import FLT.Mazur.WeierstrassSuccessiveShearConicCoefficient

/-!
# The separate scale-one conic under coefficient specialization

The full original conic maps retain incidence, root-shifted slope and the
vanishing horizontal coordinate. Their coefficient comparison keeps the
scale-one conic constant and works for arbitrary coefficient algebras.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassSuccessiveX
open WeierstrassDividedDepth WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (s π b3 b4 b6 : R)
  (S : Type u) [CommRing S] [Algebra R S] (r : S)
  (hs : algebraMap R S s = 1) (hp : algebraMap R S π = 0)
  (h3 : algebraMap R S b3 = 0) (h4 : algebraMap R S b4 = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
local notation "a" => (rootShearCurve (W.map (algebraMap R S)) r).a₁
local notation "c" => algebraMap R S b6
local notation "CS" => tensorShearScaleOneConicMap W s π b3 b4 b6 S r hs hp h3 h4 hr

/-- Restrict the actual original integral chart functions to its whole conic. -/
def originalShearScaleOneConicMap : Coordinate W s π b3 b4 b6 →ₐ[R] ConicCoordinate a c :=
  ((CS).restrictScalars R).comp Algebra.TensorProduct.includeRight

/-- All original conic functions retain the incidence and unsheared slope. -/
@[simp] theorem originalShearScaleOneConicMap_coord (i : Fin 3) :
    originalShearScaleOneConicMap W s π b3 b4 b6 S r hs hp h3 h4 hr
      (coord W s π b3 b4 b6 i) = ![conicT a c, conicV a c + algebraMap S _ r, 0] i :=
  tensorShearScaleOneConicMap_coord W s π b3 b4 b6 S r hs hp h3 h4 hr i

open AlgebraicGeometry CategoryTheory in
/-- The original conic restriction factors through its actual tensor chart. -/
theorem originalShearScaleOneConicMap_spec :
    Spec.map (CommRingCat.ofHom (CS).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
          Coordinate W s π b3 b4 b6 →ₐ[R] ScalarExtension W s π b3 b4 b6 S).toRingHom) =
      Spec.map (CommRingCat.ofHom
        (originalShearScaleOneConicMap W s π b3 b4 b6 S r hs hp h3 h4 hr).toRingHom) := by
  rw [← Spec.map_comp]
  rfl

variable (T : Type u) [CommRing T] [Algebra R T] (f : S →ₐ[R] T) (t : T)
  (gs : algebraMap R T s = 1) (gp : algebraMap R T π = 0)
  (g3 : algebraMap R T b3 = 0) (g4 : algebraMap R T b4 = 0)
  (ht : t ^ 2 + algebraMap R T W.a₁ * t - algebraMap R T W.a₂ = 0)
local notation "b" => (rootShearCurve (W.map (algebraMap R T)) t).a₁
local notation "d" => algebraMap R T b6

/-- Coefficient change preserves every original integral conic function. -/
theorem originalShearScaleOneConicMap_coefficient (hrt : f r = t) :
    (conicCoefficientAlgHom a c b d f (rootShearTangent_coefficient W S r T f t hrt)
        (f.commutes b6)).comp
        (originalShearScaleOneConicMap W s π b3 b4 b6 S r hs hp h3 h4 hr) =
      originalShearScaleOneConicMap W s π b3 b4 b6 T t gs gp g3 g4 ht := by
  apply hom_ext
  intro i
  simp only [AlgHom.comp_apply, originalShearScaleOneConicMap_coord]
  fin_cases i
  · exact conicCoefficientMap_t f.toRingHom a c b d
      (rootShearTangent_coefficient W S r T f t hrt) (f.commutes b6)
  · change conicCoefficientMap f.toRingHom a c b d
      (rootShearTangent_coefficient W S r T f t hrt) (f.commutes b6)
      (conicV a c + algebraMap S _ r) = conicV b d + algebraMap T _ t
    rw [map_add, conicCoefficientMap_v, conicCoefficientMap_scalar]
    change conicV b d + algebraMap T _ (f r) = _
    rw [hrt]
  · exact map_zero _

end FLT.Mazur.WeierstrassSuccessiveX
