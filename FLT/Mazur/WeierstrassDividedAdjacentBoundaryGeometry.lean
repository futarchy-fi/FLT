/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedAdjacentBoundaryAlgebra

/-!
# The adjacent tensor transition retains the actual preceding attachment

Identify the corrected algebra transition with the original next-boundary
parameter map and preceding attachment. The complete tensor square retains
its integral projections and is cartesian.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {k : ℕ}
  (d : Data W π (k + 1)) (e : Data W π (k + 1 + 1))
local notation "x" => WeierstrassDilatation.x W (π ^ k * π) d.b3 d.b4 d.b6
local notation "u₀" => coord W (π ^ (k + 1)) π e.b3 e.b4 e.b6 2
local notation "a" => adjacentBoundaryEquiv hπ d e

/-- The algebra comparison is exactly the original pair of boundary identifications. -/
theorem adjacentBoundaryEquiv_spec :
    Spec.map (CommRingCat.ofHom (a).toRingHom) =
      Spec.map (CommRingCat.ofHom (previousBoundaryEquiv hπ d e).toRingHom) ≫
        (nextBoundaryIso d).hom := by
  change Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp]
  rfl

/-- The true preceding attachment is recovered, including the original scale correction. -/
@[reassoc] theorem adjacentBoundaryEquiv_previousToX :
    Spec.map (CommRingCat.ofHom (a).toRingHom) ≫
      (nextBoundaryIso d).inv ≫ previousToX hπ d e =
        horizontalOpenInclusion W (π ^ (k + 1)) π e.b3 e.b4 e.b6 := by
  rw [adjacentBoundaryEquiv_spec, Category.assoc, Iso.hom_inv_id_assoc]
  exact previousBoundaryEquiv_previousToX hπ d e

variable (S : Type u) [CommRing S] [Algebra R S]
local notation "O" => TensorDividedOpen W (π ^ k) π d.b3 d.b4 d.b6 S
local notation "H" => Localization.Away (tensorCoord W (π ^ (k + 1)) π e.b3 e.b4 e.b6 S 2)
local notation "qx" => Spec.map (CommRingCat.ofHom
  (AlgHom.toRingHom (PrincipalOpenTensor.coefficient (R := R) S x)))
local notation "qu" => Spec.map (CommRingCat.ofHom
  (AlgHom.toRingHom (PrincipalOpenTensor.coefficient (R := R) S u₀)))

/-- The entire adjacent tensor horizontal transition as an isomorphism of schemes. -/
def tensorAdjacentBoundaryIso : Spec (.of H) ≅ Spec (.of O) :=
  Scheme.Spec.mapIso (tensorAdjacentBoundaryEquiv hπ d e S).toRingEquiv.toCommRingCatIso.op

/-- Every original integral localized function is retained by the full tensor transition. -/
@[reassoc] theorem tensorAdjacentBoundaryIso_projection :
    (tensorAdjacentBoundaryIso hπ d e S).hom ≫ qx =
      qu ≫ Spec.map (CommRingCat.ofHom (a).toRingHom) := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext (tensorAdjacentBoundaryEquiv_coefficient hπ d e S)

/-- The integral transition and both complete coefficient projections form a pullback. -/
theorem tensorAdjacentBoundaryIso_isPullback :
    IsPullback (tensorAdjacentBoundaryIso hπ d e S).hom qu qx
      (Spec.map (CommRingCat.ofHom (a).toRingHom)) := by
  let e₀ := Scheme.Spec.mapIso (a).toRingEquiv.toCommRingCatIso.op
  change IsPullback _ _ _ e₀.hom
  exact IsPullback.of_horiz_isIso ⟨tensorAdjacentBoundaryIso_projection hπ d e S⟩

/-- After coefficient extension the transition still projects to the original attachment. -/
@[reassoc] theorem tensorAdjacentBoundaryIso_previousToX :
    (tensorAdjacentBoundaryIso hπ d e S).hom ≫ qx ≫
      (nextBoundaryIso d).inv ≫ previousToX hπ d e =
        qu ≫ horizontalOpenInclusion W (π ^ (k + 1)) π e.b3 e.b4 e.b6 := by
  rw [tensorAdjacentBoundaryIso_projection_assoc]
  exact congrArg (fun f => qu ≫ f) (adjacentBoundaryEquiv_previousToX hπ d e)

end FLT.Mazur.WeierstrassDividedDepth
