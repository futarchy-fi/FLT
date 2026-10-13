/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassIncidenceShearNormalForm
public import FLT.Mazur.WeierstrassModificationXFiberConic

/-!
# The original integral incidence line for an arbitrary tangent root

The entire affine line retains incidence zero and the root-shifted slope.
-/

@[expose] public noncomputable section
open Polynomial
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

/-- Restrict the full original tensor incidence equation to its affine line. -/
def tensorShearInitialLineMap : ScalarExtension W s b3 b4 b6 S →ₐ[S] S[X] :=
  (fiberIncidenceMap a c).comp (E).toAlgHom
local notation "F" => tensorShearInitialLineMap W s b3 b4 b6 S r hs h3 h4 hr

/-- Incidence vanishes on the entire line. -/
theorem tensorShearInitialLineMap_t : F ((1 : S) ⊗ₜ[R] t W s b3 b4 b6) = 0 := by
  change fiberIncidenceMap a c (E _) = _
  rw [tensorShearNormalEquiv_t, fiberIncidenceMap_t]

/-- The original slope includes the chosen tangent root. -/
theorem tensorShearInitialLineMap_v :
    F ((1 : S) ⊗ₜ[R] v W s b3 b4 b6) = X + C r := by
  change fiberIncidenceMap a c (E _) = _
  rw [tensorShearNormalEquiv_v, map_add, fiberIncidenceMap_v, AlgHom.commutes]
  rfl

/-- The full affine incidence line with every original integral function retained. -/
def originalShearInitialLineMap : Coordinate W s b3 b4 b6 →ₐ[R] S[X] :=
  ((F).restrictScalars R).comp Algebra.TensorProduct.includeRight
local notation "L" => originalShearInitialLineMap W s b3 b4 b6 S r hs h3 h4 hr

/-- The original incidence generator vanishes on the complete line. -/
theorem originalShearInitialLineMap_t : L (t W s b3 b4 b6) = 0 :=
  tensorShearInitialLineMap_t W s b3 b4 b6 S r hs h3 h4 hr

/-- The original slope is the full translated affine parameter. -/
theorem originalShearInitialLineMap_v : L (v W s b3 b4 b6) = X + C r :=
  tensorShearInitialLineMap_v W s b3 b4 b6 S r hs h3 h4 hr

end FLT.Mazur.WeierstrassModificationX
