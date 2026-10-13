/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveShearScaleOneConicCoefficient
public import FLT.Mazur.WeierstrassModificationXConicIncidenceOrientation

/-!
# The full incidence line in the original scale-one retained chart

The horizontal component keeps its complete slope and original root shift.
Its two markings agree with the original conic sections for every constant.
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
  (hs : algebraMap R S s = 1) (hp : algebraMap R S π = 0)
  (h3 : algebraMap R S b3 = 0) (h4 : algebraMap R S b4 = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
local notation "a" => (rootShearCurve (W.map (algebraMap R S)) r).a₁
local notation "c" => algebraMap R S b6
local notation "E" => tensorShearScaleOneFiberEquiv W s π b3 b4 b6 S r hs hp h3 h4 hr

/-- The entire scale-one incidence line, with its original polynomial slope. -/
def tensorShearScaleOneIncidenceMap : ScalarExtension W s π b3 b4 b6 S →ₐ[S] S[X] :=
  (fiberIncidenceMap a c).comp (E).toAlgHom
local notation "L" => tensorShearScaleOneIncidenceMap W s π b3 b4 b6 S r hs hp h3 h4 hr

/-- Every original retained coordinate on the full incidence line. -/
theorem tensorShearScaleOneIncidenceMap_coord (i : Fin 3) :
    L (tensorCoord W s π b3 b4 b6 S i) = ![0, X + C r, X * (X + C a)] i := by
  change fiberIncidenceMap a c (E _) = _
  rw [tensorShearScaleOneFiberEquiv_coord]
  fin_cases i <;> simp
  ring

/-- The whole incidence map on the integral chart before coefficient extension. -/
def originalShearScaleOneIncidenceMap : Coordinate W s π b3 b4 b6 →ₐ[R] S[X] :=
  ((L).restrictScalars R).comp Algebra.TensorProduct.includeRight

/-- Original integral coordinates retain exactly the same full slope formulas. -/
theorem originalShearScaleOneIncidenceMap_coord (i : Fin 3) :
    originalShearScaleOneIncidenceMap W s π b3 b4 b6 S r hs hp h3 h4 hr
      (coord W s π b3 b4 b6 i) = ![0, X + C r, X * (X + C a)] i :=
  tensorShearScaleOneIncidenceMap_coord W s π b3 b4 b6 S r hs hp h3 h4 hr i

variable (ha : IsUnit (rootShearCurve (W.map (algebraMap R S)) r).a₁)
local notation "C₀" => tensorShearScaleOneConicMap W s π b3 b4 b6 S r hs hp h3 h4 hr

/-- The first slope origin is the first original conic incidence marking. -/
theorem tensorShearScaleOneIncidenceMap_first :
    (aeval (0 : S)).comp L = (conicFirstIncidencePoint a c ha).comp C₀ := by
  apply Algebra.TensorProduct.ext_ring
  apply hom_ext
  intro i
  change aeval (0 : S) (L (tensorCoord W s π b3 b4 b6 S i)) =
    conicFirstIncidencePoint a c ha (C₀ (tensorCoord W s π b3 b4 b6 S i))
  rw [tensorShearScaleOneIncidenceMap_coord, tensorShearScaleOneConicMap_coord]
  fin_cases i <;> simp [conicFirstIncidencePoint_t, conicFirstIncidencePoint_v]

/-- The opposite slope origin is the opposite original conic incidence marking. -/
theorem tensorShearScaleOneIncidenceMap_second :
    (aeval (-a)).comp L = (conicSecondIncidencePoint a c ha).comp C₀ := by
  apply Algebra.TensorProduct.ext_ring
  apply hom_ext
  intro i
  change aeval (-a) (L (tensorCoord W s π b3 b4 b6 S i)) =
    conicSecondIncidencePoint a c ha (C₀ (tensorCoord W s π b3 b4 b6 S i))
  rw [tensorShearScaleOneIncidenceMap_coord, tensorShearScaleOneConicMap_coord]
  fin_cases i <;> simp [conicSecondIncidencePoint_t, conicSecondIncidencePoint_v]

end FLT.Mazur.WeierstrassSuccessiveX
