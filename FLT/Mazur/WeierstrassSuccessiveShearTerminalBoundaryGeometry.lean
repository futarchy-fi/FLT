/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveShearTerminalConicBranches
public import FLT.Mazur.PrincipalOpenTensorGeometry

/-!
# Terminal node boundary geometry retains the original tensor transition

The normalized node restriction is exactly the composite of the full conic
incidence isomorphism and the actual integral depth overlap.
-/

@[expose] public noncomputable section
open scoped TensorProduct
namespace FLT.Mazur.WeierstrassSuccessiveX
open WeierstrassDividedDepth WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (π : R)
  (k : ℕ) (b3 b4 b6 : R) (S : Type u) [CommRing S] [Algebra R S] (r : S)
  (hs : algebraMap R S (π ^ k) = 0) (hp : algebraMap R S π = 0)
  (h3 : algebraMap R S b3 = 0) (h4 : algebraMap R S b4 = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
local notation "U" => rootShearCurve (W.map (algebraMap R S)) r
local notation "c" => algebraMap R S b6
local notation "C₀" => ConicCoordinate (U).a₁ c
local notation "B" => MiddleConicOpen U c
local notation "T₀" => ScalarExtension W (π ^ k) π b3 b4 b6 S
local notation "D" => S ⊗[R] WeierstrassDilatation.Coordinate W (π ^ (k + 1)) b3 b4 b6
local notation "x" => WeierstrassDilatation.x W (π ^ (k + 1)) b3 b4 b6
local notation "y" => WeierstrassDilatation.y W (π ^ (k + 1)) b3 b4 b6
local notation "t" => coord W (π ^ k) π b3 b4 b6 0
variable (h6 : algebraMap R S b6 = 0)
  (a : Sˣ) (ha : (a : S) = (rootShearCurve (W.map (algebraMap R S)) r).a₁)
local notation "hsNext" => show algebraMap R S (π ^ (k + 1)) = 0 from by
  rw [pow_succ, map_mul, hp, mul_zero]
local notation "E" => tensorShearTerminalNodeEquiv W π k b3 b4 b6 S r hp h3 h4 hr h6 a ha
local notation "φ" => tensorShearTerminalConicMap W π k b3 b4 b6 S r hs hp h3 h4 hr
local notation "v" => conicBoundaryUnit U c
local notation "tx" => (1 : S) ⊗ₜ[R] x
local notation "ty" => (1 : S) ⊗ₜ[R] y

open AlgebraicGeometry CategoryTheory
local notation "ψ" => tensorShearTerminalNodeConicMap W π k b3 b4 b6 S r
  hs hp h3 h4 hr h6 a ha
local notation "C" => tensorShearConicBoundaryIso W (π ^ k) π b3 b4 b6 S r hs hp h3 h4 hr
local notation "A" => PrincipalOpenTensor.transitionIso S x t
  (depthOverlapEquiv W π k b3 b4 b6)
local notation "N" => Scheme.Spec.mapIso (E).toRingEquiv.toCommRingCatIso.op
local notation "b" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom ψ))

/-- The whole node comparison restricts along the original conic tensor boundary. -/
@[reassoc] theorem tensorShearTerminalNodeConicMap_boundary :
    b ≫ (N).hom = (C).hom ≫ (A).hom ≫ PrincipalOpenTensor.inclusion S x := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  change φ ((E).symm ((E) z)) = _
  rw [AlgEquiv.symm_apply_apply]
  rfl

end FLT.Mazur.WeierstrassSuccessiveX
