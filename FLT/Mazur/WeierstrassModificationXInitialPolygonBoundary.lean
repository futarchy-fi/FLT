/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXInitialPolygonChart
public import FLT.Mazur.WeierstrassModificationXStandardPunctureEquiv
public import FLT.Mazur.NodalFiberUnitScalingBoundary
public import FLT.Mazur.NodalFiberUnitScalingPunctureRange

/-!
# The full initial boundary in its actual polygon coordinates

The parameter is the entire original corrected incidence, not its residue.
The full original Laurent isomorphism proves that this change is invertible.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (I : Ideal R) (hI : IsNilpotent I) (ha : IsUnit W.a₁) (hs : s ∈ I)
  (h2 : W.a₂ ∈ I) (h3 : b3 ∈ I) (h4 : b4 ∈ I) (h6 : b6 ∈ I)
local notation "N" => NodalFiber.Coordinate s
local notation "L" => PolynomialNodeOpen W s
local notation "D" => Localization.Away (NodalFiber.p s)
local notation "G" => laurentNodeRestriction W s b3 b4 b6 I hI ha hs h2 h3 h4 h6
local notation "E" => AlgHom.comp (G) (Algebra.algHom R N L)
local notation "hp" => laurentNodeRestriction_p_unit W s b3 b4 b6 I hI ha hs h2 h3 h4 h6
local notation "e" => NodalFiber.unitSmoothingIso s s 1 (by simp)
local notation "B" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom (G)))

/-- The entire original corrected first node coordinate is a Laurent unit. -/
def initialPolygonBoundaryUnit : R[T;T⁻¹]ˣ :=
  NodalFiber.unitNormalizedFirstUnit s 1 E hp

/-- The full corrected incidence determines the actual initial boundary parameter. -/
def initialPolygonBoundaryParameter : PolygonSmoothing.branchTorus R ⟶
    PolygonSmoothing.branchTorus R :=
  Spec.map (CommRingCat.ofHom (LaurentUnitPoints.evalUnit (R := R)
    (initialPolygonBoundaryUnit W s b3 b4 b6 I hI ha hs h2 h3 h4 h6)).toRingHom)

local notation "T" => initialPolygonBoundaryParameter W s b3 b4 b6 I hI ha hs h2 h3 h4 h6

/-- Every original initial boundary function survives the polygon comparison. -/
@[reassoc] theorem initialPolygonChart_boundary :
    B ≫ initialPolygonChart W s = T ≫ PolygonSmoothing.leftBranchOpen R s := by
  rw [initialPolygonChart, ← Category.assoc, ← Spec.map_comp]
  exact NodalFiber.unitSmoothingIso_first_boundary s s 1 (by simp) E hp

/-- The original full initial boundary occupies the whole first puncture after comparison. -/
theorem initialPolygonChart_boundary_range :
    Set.range (B ≫ initialPolygonChart W s) =
      Set.range (PolygonSmoothing.leftBranchOpen R s) := by
  have hr : Set.range (Spec.map (CommRingCat.ofHom (E).toRingHom)) =
      (PrimeSpectrum.basicOpen (NodalFiber.p s) : Set (PrimeSpectrum N)) := by
    rw [← initialStandardPunctureIso_node W s b3 b4 b6 I hI ha hs h2 h3 h4 h6]
    change Set.range (PrimeSpectrum.comap (algebraMap N D) ∘
      (initialStandardPunctureIso W s b3 b4 b6 I hI ha hs h2 h3 h4 h6).hom) = _
    let i := initialStandardPunctureIso W s b3 b4 b6 I hI ha hs h2 h3 h4 h6
    exact (i.hom.homeomorph.surjective.range_comp _).trans
      (PrimeSpectrum.localization_away_comap_range D _)
  rw [initialPolygonChart, ← Category.assoc, ← Spec.map_comp]
  exact NodalFiber.unitSmoothingIso_comp_range s s 1 (by simp) _ true hr

/-- The actual original initial parameter change is an isomorphism of the whole Laurent torus. -/
instance initialPolygonBoundaryParameter_isIso : IsIso T := by
  let f := B ≫ initialPolygonChart W s
  let b := PolygonSmoothing.leftBranchOpen R s
  let _ : IsOpenImmersion (Spec.map (CommRingCat.ofHom (E).toRingHom)) := by
    rw [← initialStandardPunctureIso_node W s b3 b4 b6 I hI ha hs h2 h3 h4 h6]
    let _ : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap N D))) :=
      IsOpenImmersion.of_isLocalization (NodalFiber.p s)
    infer_instance
  let _ : IsOpenImmersion f := by
    dsimp [f]
    rw [initialPolygonChart, ← Category.assoc, ← Spec.map_comp]
    exact IsOpenImmersion.comp (Spec.map (CommRingCat.ofHom (E).toRingHom)) (e).hom
  let i := IsOpenImmersion.isoOfRangeEq f b
    (initialPolygonChart_boundary_range W s b3 b4 b6 I hI ha hs h2 h3 h4 h6)
  have he : T = i.hom := by
    apply (cancel_mono b).mp
    exact (initialPolygonChart_boundary W s b3 b4 b6 I hI ha hs h2 h3 h4 h6).symm.trans
      (IsOpenImmersion.isoOfRangeEq_hom_fac f b _).symm
  rw [he]
  infer_instance

end FLT.Mazur.WeierstrassModificationX
