/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveOppositeNodeChart
public import FLT.Mazur.QuadraticRootBranchCoverage

/-!
# The two constructed polygon node charts cover the original successive chart

Transport of the quadratic branch cover through the actual monic and polygon
coordinate isomorphisms gives preimages under the original scheme morphisms.
This covers one successive chart, not the global stage's boundary atlas.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassSuccessiveX
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s π b3 b4 b6 : R)
  (r : SuccessiveIncidence.Coordinate π)
  (hr : r ^ 2 + nodeSlopeLinear W π b3 * r = nodeSlopeConstant W s π b4 b6)
local notation "a" => nodeSlopeLinear W π b3
local notation "b" => nodeSlopeConstant W s π b4 b6

/-- Every point of the incidence root section lifts through the actual polygon chart. -/
theorem simpleSlopePolygonChart_lift (x : PrimeSpectrum (SuccessiveIncidence.Coordinate π)) :
    ∃ y, simpleSlopePolygonChart W s π b3 b4 b6 r hr y =
      PrimeSpectrum.comap (toMonic W s π b3 b4 b6).toRingHom
        (PrimeSpectrum.comap
          (QuadraticRootBranchLocalization.evaluation a b r hr).toRingHom x) := by
  refine ⟨PrimeSpectrum.comap (SuccessiveIncidence.fromPolygon π).toRingHom x, ?_⟩
  have hx : PrimeSpectrum.comap (SuccessiveIncidence.toPolygon π).toRingHom
      (PrimeSpectrum.comap (SuccessiveIncidence.fromPolygon π).toRingHom x) = x :=
    (PrimeSpectrum.comapEquiv (SuccessiveIncidence.polygonEquiv π).toRingEquiv).left_inv x
  change PrimeSpectrum.comap (toMonic W s π b3 b4 b6).toRingHom
    (PrimeSpectrum.comap (QuadraticRootBranchLocalization.evaluation a b r hr).toRingHom
      (PrimeSpectrum.comap (SuccessiveIncidence.toPolygon π).toRingHom
        (PrimeSpectrum.comap (SuccessiveIncidence.fromPolygon π).toRingHom x))) = _
  rw [hx]

/-- The two original simple-root polygon charts cover the whole successive spectrum. -/
theorem simpleSlopePolygonCharts_cover (hu : IsUnit (r + r + a))
    (p : Spec (.of (Coordinate W s π b3 b4 b6))) :
    (∃ x, simpleSlopePolygonChart W s π b3 b4 b6 r hr x = p) ∨
      ∃ x, simpleSlopePolygonChart W s π b3 b4 b6
        (QuadraticRootBranchLocalization.oppositeRoot a r)
        (QuadraticRootBranchLocalization.oppositeRoot_equation a b r hr) x = p := by
  let e := PrimeSpectrum.comapEquiv (monicEquiv W s π b3 b4 b6).toRingEquiv
  have hp : PrimeSpectrum.comap (toMonic W s π b3 b4 b6).toRingHom (e p) = p :=
    e.left_inv p
  obtain h | h := QuadraticRootBranchLocalization.rootCharts_cover a b r hr hu (e p)
  · obtain ⟨x, hx⟩ := h
    obtain ⟨y, hy⟩ := simpleSlopePolygonChart_lift W s π b3 b4 b6 r hr x
    exact Or.inl ⟨y, hy.trans ((congrArg
      (PrimeSpectrum.comap (toMonic W s π b3 b4 b6).toRingHom) hx).trans hp)⟩
  · obtain ⟨x, hx⟩ := h
    obtain ⟨y, hy⟩ := simpleSlopePolygonChart_lift W s π b3 b4 b6
      (QuadraticRootBranchLocalization.oppositeRoot a r)
      (QuadraticRootBranchLocalization.oppositeRoot_equation a b r hr) x
    exact Or.inr ⟨y, hy.trans ((congrArg
      (PrimeSpectrum.comap (toMonic W s π b3 b4 b6).toRingHom) hx).trans hp)⟩

variable (I : Ideal R) (hI : IsNilpotent I) (ha : IsUnit W.a₁) (hs : s ∈ I) (h2 : W.a₂ ∈ I)
  (h3 : b3 ∈ I) (h4 : b4 ∈ I) (h6 : b6 ∈ I)

/-- The constructed nilpotent and opposite node charts cover the original successive chart. -/
theorem nilpotentPolygonCharts_cover (p : Spec (.of (Coordinate W s π b3 b4 b6))) :
    (∃ x, nilpotentPolygonChart W s π b3 b4 b6 I hI ha hs h2 h3 h4 h6 x = p) ∨
      ∃ x, oppositePolygonChart W s π b3 b4 b6 I hI ha hs h2 h3 h4 h6 x = p := by
  have he : simpleSlopeRetraction W s π b3 b4 b6
      (nilpotentNodeSlope W s π b3 b4 b6 I hI ha hs h2 h3 h4 h6)
      (nilpotentNodeSlope_equation W s π b3 b4 b6 I hI ha hs h2 h3 h4 h6) =
        nilpotentNodeRetraction W s π b3 b4 b6 I hI ha hs h2 h3 h4 h6 :=
    nilpotentNodeRetraction_monic W s π b3 b4 b6 I hI ha hs h2 h3 h4 h6
  have h := simpleSlopePolygonCharts_cover W s π b3 b4 b6 _
    (nilpotentNodeSlope_equation W s π b3 b4 b6 I hI ha hs h2 h3 h4 h6)
    (nilpotentNodeSlope_simple W s π b3 b4 b6 I hI ha hs h2 h3 h4 h6) p
  simpa only [simpleSlopePolygonChart, he, nilpotentPolygonChart, nilpotentNodeChart,
    oppositePolygonChart, oppositeNodeSlope] using h

end FLT.Mazur.WeierstrassSuccessiveX
