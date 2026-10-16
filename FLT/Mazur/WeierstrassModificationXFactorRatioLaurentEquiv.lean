/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXFactorRatioLaurentUnit
public import FLT.Mazur.WeierstrassModificationXPolynomialFactorRatioBoundary
public import FLT.Mazur.LaurentNilpotentReparametrization

/-!
# The corrected retained Laurent boundary is an isomorphism

The exact squared-factor parameter gives an automorphism of the whole Laurent
algebra and identifies the original full boundary with the standard polygon edge.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (ha : IsUnit W.a₁)
  (s : R) (b3 b4 b6 : R) (I : Ideal R) (hI : IsNilpotent I) (hs : s ∈ I)
  (h2 : W.a₂ ∈ I) (h3 : b3 ∈ I) (h4 : b4 ∈ I) (h6 : b6 ∈ I)
local notation "B" => R[T;T⁻¹]
local notation "u" => factorRatioLaurentUnit W ha s b3 b4 b6 I hI hs h2 h3 h4 h6
local notation "G" => laurentNodeRestriction W s b3 b4 b6 I hI ha hs h2 h3 h4 h6
local notation "r₀" => polynomialSlopeRoot W b3 b4 b6 I hI ha h2 h3 h4 h6
local notation "hr₀" => polynomialSlopeRoot_equation W b3 b4 b6 I hI ha h2 h3 h4 h6
local notation "hm₀" => polynomialSlopeRoot_mem W b3 b4 b6 I hI ha h2 h3 h4 h6

/-- The full corrected boundary substitution is an algebra automorphism at arbitrary order. -/
def factorRatioLaurentEquiv : B ≃ₐ[R] B :=
  LaurentNilpotentReparametrization.equiv I hI u
    (factorRatioLaurentUnit_sub_mem W ha s b3 b4 b6 I hI hs h2 h3 h4 h6)

local notation "e" => factorRatioLaurentEquiv W ha s b3 b4 b6 I hI hs h2 h3 h4 h6

/-- The constructed substitution retains every arithmetic correction in the original unit. -/
theorem factorRatioLaurentEquiv_toAlgHom : (e).toAlgHom = LaurentUnitPoints.evalUnit u := rfl

/-- The positive generator becomes exactly the corrected original first boundary coordinate. -/
theorem factorRatioLaurentEquiv_T : e (LaurentPolynomial.T 1) = (u : B) := by
  change LaurentUnitPoints.evalUnit u (LaurentPolynomial.T 1) = _
  rw [LaurentUnitPoints.evalUnit_T, zpow_one]

/-- The original retained Laurent scheme has the full corrected isomorphic parametrization. -/
def factorRatioLaurentIso : Spec (.of B) ≅ Spec (.of B) :=
  Scheme.Spec.mapIso (e).toRingEquiv.toCommRingCatIso.op

local notation "E" => factorRatioLaurentIso W ha s b3 b4 b6 I hI hs h2 h3 h4 h6
variable (τ : R) (hτ : s = W.a₁ ^ 2 * τ)
local notation "C" => polynomialFactorRatioChart W ha s τ hτ b3 b4 b6 r₀ hr₀ I hI hm₀ h3

/-- The actual original full Laurent restriction has the exact corrected polygon boundary square. -/
@[reassoc] theorem factorRatioLaurentIso_boundary :
    Spec.map (CommRingCat.ofHom (G).toRingHom) ≫ C =
      (E).hom ≫ PolygonSmoothing.leftBranchOpen R τ := by
  rw [polynomialFactorRatioChart_eq_spec, ← Spec.map_comp]
  apply PolygonSmoothing.boundary_leftBranchOpen τ
    ((G).comp (polynomialFactorRatioEvaluation W ha s τ hτ b3 b4 b6 r₀ hr₀ I hI hm₀ h3)) u
  rw [AlgHom.comp_apply, polynomialFactorRatioEvaluation_left]
  exact factorRatioLaurentUnit_coordinate W ha s b3 b4 b6 I hI hs h2 h3 h4 h6 τ hτ

/-- The inverse reparametrization recovers the entire standard polygon edge. -/
@[reassoc] theorem factorRatioLaurentIso_inv_boundary :
    (E).inv ≫ Spec.map (CommRingCat.ofHom (G).toRingHom) ≫ C =
      PolygonSmoothing.leftBranchOpen R τ := by
  rw [factorRatioLaurentIso_boundary, Iso.inv_hom_id_assoc]

/-- The original full boundary and the standard polygon edge have exactly the same range. -/
theorem factorRatioLaurent_boundary_range :
    Set.range (Spec.map (CommRingCat.ofHom (G).toRingHom) ≫ C) =
      Set.range (PolygonSmoothing.leftBranchOpen R τ) := by
  rw [factorRatioLaurentIso_boundary]
  change Set.range ((PolygonSmoothing.leftBranchOpen R τ) ∘ (E).hom) = _
  exact (E).hom.homeomorph.surjective.range_comp _

end FLT.Mazur.WeierstrassModificationX
