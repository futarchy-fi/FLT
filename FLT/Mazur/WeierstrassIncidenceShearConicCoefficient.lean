/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassIncidenceShearNormalForm
public import FLT.Mazur.WeierstrassSuccessiveShearConicCoefficient

/-!
# The full initial conic under arbitrary-root coefficient specialization

Restrict the original initial tensor equation to the entire conic. Both
original generators, including the root-shifted slope, specialize correctly.
-/

@[expose] public noncomputable section
open scoped TensorProduct
namespace FLT.Mazur.WeierstrassModificationX
open WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (S : Type u) [CommRing S] [Algebra R S] (r : S)
  (hs : algebraMap R S s = 0) (h3 : algebraMap R S b3 = 0)
  (h4 : algebraMap R S b4 = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
local notation "a" => (rootShearCurve (W.map (algebraMap R S)) r).a₁
local notation "c" => algebraMap R S b6
local notation "E" => tensorShearNormalEquiv W s b3 b4 b6 S r hs h3 h4 hr

/-- Restriction of the original tensor incidence equation to the complete initial conic. -/
def tensorShearInitialConicMap : ScalarExtension W s b3 b4 b6 S →ₐ[S] ConicCoordinate a c :=
  (fiberConicMap a c).comp (E).toAlgHom

local notation "F" => tensorShearInitialConicMap W s b3 b4 b6 S r hs h3 h4 hr

/-- The original incidence generator remains the full conic coordinate. -/
theorem tensorShearInitialConicMap_t :
    F ((1 : S) ⊗ₜ[R] t W s b3 b4 b6) = conicT a c := by
  change fiberConicMap a c (E _) = _
  rw [tensorShearNormalEquiv_t, fiberConicMap_t]

/-- The original slope retains the chosen tangent root on the entire conic. -/
theorem tensorShearInitialConicMap_v :
    F ((1 : S) ⊗ₜ[R] v W s b3 b4 b6) = conicV a c + algebraMap S _ r := by
  change fiberConicMap a c (E _) = _
  rw [tensorShearNormalEquiv_v, map_add, fiberConicMap_v, AlgHom.commutes]

/-- Restrict every original integral initial-chart function to the full sheared conic. -/
def originalShearInitialConicMap : Coordinate W s b3 b4 b6 →ₐ[R] ConicCoordinate a c :=
  ((F).restrictScalars R).comp Algebra.TensorProduct.includeRight

/-- The complete integral incidence restriction keeps its coordinate. -/
theorem originalShearInitialConicMap_t :
    originalShearInitialConicMap W s b3 b4 b6 S r hs h3 h4 hr (t W s b3 b4 b6) =
      conicT a c := tensorShearInitialConicMap_t W s b3 b4 b6 S r hs h3 h4 hr

/-- The complete integral slope restriction keeps its root shift. -/
theorem originalShearInitialConicMap_v :
    originalShearInitialConicMap W s b3 b4 b6 S r hs h3 h4 hr (v W s b3 b4 b6) =
      conicV a c + algebraMap S _ r :=
  tensorShearInitialConicMap_v W s b3 b4 b6 S r hs h3 h4 hr

variable (T : Type u) [CommRing T] [Algebra R T] (f : S →ₐ[R] T) (r' : T)
  (gs : algebraMap R T s = 0) (g3 : algebraMap R T b3 = 0)
  (g4 : algebraMap R T b4 = 0)
  (hr' : r' ^ 2 + algebraMap R T W.a₁ * r' - algebraMap R T W.a₂ = 0)
local notation "b" => (rootShearCurve (W.map (algebraMap R T)) r').a₁
local notation "d" => algebraMap R T b6

/-- Actual coefficient specialization preserves every original initial conic function. -/
theorem originalShearInitialConicMap_coefficient (hrt : f r = r') :
    (conicCoefficientAlgHom a c b d f
        (WeierstrassSuccessiveX.rootShearTangent_coefficient W S r T f r' hrt)
        (f.commutes b6)).comp
        (originalShearInitialConicMap W s b3 b4 b6 S r hs h3 h4 hr) =
      originalShearInitialConicMap W s b3 b4 b6 T r' gs g3 g4 hr' := by
  apply hom_ext
  · change conicCoefficientMap f.toRingHom a c b d
      (WeierstrassSuccessiveX.rootShearTangent_coefficient W S r T f r' hrt)
      (f.commutes b6)
      (originalShearInitialConicMap W s b3 b4 b6 S r hs h3 h4 hr (t W s b3 b4 b6)) = _
    rw [originalShearInitialConicMap_t, originalShearInitialConicMap_t,
      conicCoefficientMap_t]
  · change conicCoefficientMap f.toRingHom a c b d
      (WeierstrassSuccessiveX.rootShearTangent_coefficient W S r T f r' hrt)
      (f.commutes b6)
      (originalShearInitialConicMap W s b3 b4 b6 S r hs h3 h4 hr (v W s b3 b4 b6)) = _
    rw [originalShearInitialConicMap_v, originalShearInitialConicMap_v,
      map_add, conicCoefficientMap_v, conicCoefficientMap_scalar]
    change conicV b d + algebraMap T _ (f r) = _
    rw [hrt]

end FLT.Mazur.WeierstrassModificationX
