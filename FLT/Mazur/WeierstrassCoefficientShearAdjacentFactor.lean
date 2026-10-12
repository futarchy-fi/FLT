/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearAdjacentIntersection
import all FLT.Mazur.WeierstrassCoefficientShearAdjacentIntersection
public import FLT.Mazur.WeierstrassDividedAdjacentBoundaryGeometry

/-!
# Factor the adjacent conic isomorphism through the original tensor boundaries

Keep each genuine transition as a scheme isomorphism, including the scale
correction between the two divided horizontal coordinate presentations.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {k : ℕ}
  (d : Data W π (k + 1)) (e : Data W π (k + 1 + 1))
  (S : Type u) [CommRing S] [Algebra R S] (r : S)
  (hs : algebraMap R S (π ^ k) = 0) (hp : algebraMap R S π = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
local notation "g3" => And.left (coefficientShearAdjacent_coefficients hπ d e S hp)
local notation "g4" => And.left (And.right (coefficientShearAdjacent_coefficients hπ d e S hp))
local notation "E" => tensorShearConicBoundaryIso W (π ^ k) π
  d.b3 d.b4 d.b6 S r hs hp g3 g4 hr
local notation "x" => WeierstrassDilatation.x W (π ^ k * π) d.b3 d.b4 d.b6
local notation "t" => coord W (π ^ k) π d.b3 d.b4 d.b6 0
local notation "A" => Scheme.Spec.mapIso (Iso.op (RingEquiv.toCommRingCatIso
  (AlgEquiv.toRingEquiv (tensorOverlapEquiv W (π ^ k) π d.b3 d.b4 d.b6 S))))
local notation "B" => tensorAdjacentBoundaryIso hπ d e S
local notation "J" => coefficientShearAdjacentConicIso hπ d e S r hs hp hr

/-- The adjacent conic comparison is the composite of both genuine tensor transitions. -/
theorem coefficientShearAdjacentConicIso_factor :
    (J).hom = (E).hom ≫ (A).hom ≫ (B).inv := by
  change Spec.map _ = Spec.map _ ≫ Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  rfl

end FLT.Mazur.WeierstrassDividedDepth
