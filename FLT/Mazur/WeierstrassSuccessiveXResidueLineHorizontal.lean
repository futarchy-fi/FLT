/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXResidueBoundaryDisjoint
public import FLT.Mazur.ProjectiveLineCharts

/-!
# The full horizontal boundary of each original residue line

The preceding horizontal principal open cuts out precisely the punctured
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
variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {n : ℕ} (D : SplitNodeDepth W π n)
  (k : ℕ) (hk0 : 0 < k) (hk : 2 * (k + 1) ≤ n) (b3 b4 b6 : R)
  (h3 : W.a₃ = π ^ (k + 1) * b3) (h4 : W.a₄ = π ^ (k + 1) * b4)
  (r : ResidueField R) (hr : r * (r + residue R W.a₁) = 0)
local notation "K" => ResidueField R
local notation "u₀" => coord W (π ^ k) π b3 b4 b6 2
local notation "i" => PrincipalOpenTensor.inclusion K u₀
local notation "L" => residueSuccessiveLineImmersion D k hk0 hk b3 b4 b6 h3 h4 r hr
local notation "p" => ProjectiveLine.overlapLeft K

/-- The entire preceding boundary pulls back to the line with its origin removed. -/
theorem residueLineHorizontal_preimage : L ⁻¹' Set.range i = Set.range p := by
  rw [residueSuccessiveLineImmersion_eq_spec]
  have H := PrincipalOpenVanishingIntersection.preimage
    (residueSuccessiveLineMap D k hk0 hk b3 b4 b6 h3 h4 r hr).toRingHom
    (tensorCoord W (π ^ k) π b3 b4 b6 K 2)
  exact H.trans ((congrArg (fun z : Polynomial K =>
    (PrimeSpectrum.basicOpen z : Set (PrimeSpectrum (Polynomial K))))
      (residueSuccessiveLineMap_coord D k hk0 hk b3 b4 b6 h3 h4 r hr 2)).trans
        (PrimeSpectrum.localization_away_comap_range K[T;T⁻¹] (Polynomial.X : Polynomial K)).symm)

/-- The original punctured line maps canonically into the entire horizontal principal open. -/
def residueLineToHorizontal :=
  IsOpenImmersion.lift i (p ≫ L) (by
    rintro z ⟨q, rfl⟩
    exact Set.ext_iff.mp (residueLineHorizontal_preimage D k hk0 hk b3 b4 b6 h3 h4 r hr)
      (p q) |>.mpr ⟨q, rfl⟩)

/-- The canonical lift retains the original line parameter and inclusion. -/
@[reassoc] theorem residueLineToHorizontal_comp :
    residueLineToHorizontal D k hk0 hk b3 b4 b6 h3 h4 r hr ≫ i = p ≫ L :=
  IsOpenImmersion.lift_fac _ _ _

/-- The whole punctured line is the scheme intersection with the preceding boundary. -/
theorem residueLineHorizontal_isPullback :
    IsPullback (residueLineToHorizontal D k hk0 hk b3 b4 b6 h3 h4 r hr) p i L := by
  apply IsOpenImmersion.isPullback
  · exact (residueLineToHorizontal_comp D k hk0 hk b3 b4 b6 h3 h4 r hr).symm
  · exact TopologicalSpace.Opens.ext
      (residueLineHorizontal_preimage D k hk0 hk b3 b4 b6 h3 h4 r hr)

end FLT.Mazur.WeierstrassSuccessiveX
