/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveShearComponents
public import FLT.Mazur.PrincipalOpenTensorGeometry
public import FLT.Mazur.PrincipalOpenVanishingIntersection
public import FLT.Mazur.ProjectiveLineCharts

/-!
# The full horizontal boundary of each coefficient-split original line

The original tensor horizontal principal open cuts out precisely the punctured
line. The original Laurent inclusion and its canonical horizontal lift
form a cartesian square, including all scheme structure.
-/

@[expose] public noncomputable section
open IsLocalRing AlgebraicGeometry CategoryTheory Limits
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (s π b3 b4 b6 : R)
  (S : Type u) [CommRing S] [Algebra R S] (r : S)
  (hs : algebraMap R S s = 0) (hp : algebraMap R S π = 0)
  (h3 : algebraMap R S b3 = 0) (h4 : algebraMap R S b4 = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
  (v : S) (hv : v * (v + (WeierstrassDividedDepth.rootShearCurve
    (W.map (algebraMap R S)) r).a₁) = 0)
local notation "u₀" => coord W s π b3 b4 b6 2
local notation "i" => PrincipalOpenTensor.inclusion S u₀
local notation "f" => tensorShearLineMap W s π b3 b4 b6 S r hs hp h3 h4 hr v hv
local notation "L" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom f))
local notation "p" => Spec.map (CommRingCat.ofHom
  (Polynomial.toLaurent : Polynomial S →+* S[T;T⁻¹]))

/-- The entire preceding boundary pulls back to the line with its origin removed. -/
theorem tensorShearLineHorizontal_preimage : L ⁻¹' Set.range i = Set.range p := by
  have H := PrincipalOpenVanishingIntersection.preimage
    (f).toRingHom
    (tensorCoord W s π b3 b4 b6 S 2)
  exact H.trans ((congrArg (fun z : Polynomial S =>
    (PrimeSpectrum.basicOpen z : Set (PrimeSpectrum (Polynomial S))))
      (tensorShearLineMap_coord W s π b3 b4 b6 S r hs hp h3 h4 hr v hv 2)).trans
        (PrimeSpectrum.localization_away_comap_range S[T;T⁻¹] (Polynomial.X : Polynomial S)).symm)

/-- The original punctured line maps canonically into the entire horizontal principal open. -/
def tensorShearLineToHorizontal :=
  IsOpenImmersion.lift i (p ≫ L) (by
    rintro z ⟨q, rfl⟩
    exact Set.ext_iff.mp (tensorShearLineHorizontal_preimage W s π b3 b4 b6 S r hs hp h3 h4 hr v hv)
      (p q) |>.mpr ⟨q, rfl⟩)

/-- The canonical lift retains the original line parameter and inclusion. -/
@[reassoc] theorem tensorShearLineToHorizontal_comp :
    tensorShearLineToHorizontal W s π b3 b4 b6 S r hs hp h3 h4 hr v hv ≫ i = p ≫ L :=
  IsOpenImmersion.lift_fac _ _ _

/-- The whole punctured line is the scheme intersection with the preceding boundary. -/
theorem tensorShearLineHorizontal_isPullback :
    IsPullback (tensorShearLineToHorizontal W s π b3 b4 b6 S r hs hp h3 h4 hr v hv) p i L := by
  let _ : IsOpenImmersion p := IsOpenImmersion.of_isLocalization (Polynomial.X : Polynomial S)
  apply IsOpenImmersion.isPullback
  · exact (tensorShearLineToHorizontal_comp W s π b3 b4 b6 S r hs hp h3 h4 hr v hv).symm
  · exact TopologicalSpace.Opens.ext
      (tensorShearLineHorizontal_preimage W s π b3 b4 b6 S r hs hp h3 h4 hr v hv)

end FLT.Mazur.WeierstrassSuccessiveX
