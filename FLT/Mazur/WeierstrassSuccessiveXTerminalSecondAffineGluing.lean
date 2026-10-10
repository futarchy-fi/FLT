/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXConicBoundaryCharts
public import FLT.Mazur.WeierstrassSuccessiveXTerminalLaurentRange
public import FLT.Mazur.SchemeOpenPushoutCoverIso

/-!
# Completing the original second conic parameter to the full affine line

Glue the entire original parameter open to the entire terminal Laurent
chart using the actual finite-model boundary. Their pushout is the full
second affine line, with its original coordinate and origin retained.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open scoped Polynomial LaurentPolynomial
namespace FLT.Mazur.WeierstrassSuccessiveX
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {n : ℕ} (D : SplitNodeDepth W π n)
  (k : ℕ) (hk : 2 * (k + 1) ≤ n) (b3 b4 b6 : R)
  (h3 : W.a₃ = π ^ (k + 1) * b3) (h4 : W.a₄ = π ^ (k + 1) * b4)
  (h6 : W.a₆ = (π ^ (k + 1)) ^ 2 * b6) (hp : 2 * (k + 1) = n)
local notation "K" => ResidueField R
local notation "a" => WeierstrassCurve.a₁ (W.map (residue R))
local notation "c" => residue R b6
local notation "ha" => D.a₁_unit.map (residue R)
local notation "hc" => laurentConicComponent_constant_isUnit D k b6 h6 hp
local notation "f" => conicIncidenceSecondParameterMap a c ha hc
local notation "ψ" => residueLaurentConicMap D k hk b3 b4 b6 h3 h4 h6 hp
local notation "s" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom ψ))
local notation "j" => PrincipalOpenTransport.inclusion (conicParameterPolynomial c)
local notation "r" => ProjectiveLine.overlapRight K

/-- The full original boundary maps agree in the second affine coordinate. -/
@[reassoc] theorem terminalSecondAffine_condition : f ≫ j = s ≫ r := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply Polynomial.ringHom_ext
  · intro q
    change conicIncidenceSecondParameterHom a c ha hc (algebraMap K _ q) =
      ψ (LaurentPolynomial.invert (Polynomial.toLaurent (Polynomial.C q)))
    rw [AlgHom.commutes, Polynomial.toLaurent_C, LaurentPolynomial.invert_C]
    exact ((ψ).commutes q).symm
  · change conicIncidenceSecondParameterHom a c ha hc (conicParameterZ c) =
      ψ (LaurentPolynomial.invert (Polynomial.toLaurent Polynomial.X))
    rw [conicIncidenceSecondParameterHom_z, Polynomial.toLaurent_X,
      LaurentPolynomial.invert_T]
    exact (residueLaurentConicMap_inverseParameter D k hk b3 b4 b6 h3 h4 h6 hp).symm

/-- The original finite-model boundary is the complete affine-chart intersection. -/
theorem terminalSecondAffine_isPullback : IsPullback f s j r := by
  apply IsOpenImmersion.isPullback f s j r
    (terminalSecondAffine_condition D k hk b3 b4 b6 h3 h4 h6 hp).symm
  apply TopologicalSpace.Opens.ext
  change r ⁻¹' Set.range j = Set.range s
  rw [show Set.range j =
    (PrimeSpectrum.basicOpen (conicParameterPolynomial c) : Set (PrimeSpectrum K[X])) from
      PrimeSpectrum.localization_away_comap_range _ _]
  exact (residueLaurentConicMap_range_inverseParameter D k hk b3 b4 b6 h3 h4 h6 hp).symm

omit [IsDomain R] in
/-- The parameter open and the whole inverse torus cover every point of the affine line. -/
theorem terminalSecondAffine_cover (x : ProjectiveLine.chart K) :
    (∃ y, j y = x) ∨ ∃ z, r z = x := by
  change x ∈ Set.range j ∨ x ∈ Set.range r
  rw [show Set.range j =
    (PrimeSpectrum.basicOpen (conicParameterPolynomial c) : Set (PrimeSpectrum K[X])) from
      PrimeSpectrum.localization_away_comap_range _ _, ProjectiveLine.overlapRight_range_basicOpen]
  by_cases hx : Polynomial.X ∈ x.asIdeal
  · left
    intro hf
    have hm := x.asIdeal.mul_mem_left (Polynomial.C c)
      (x.asIdeal.pow_mem_of_mem hx 2 (by decide))
    have h1 : (1 : K[X]) ∈ x.asIdeal := by
      simpa only [conicParameterPolynomial, sub_add_cancel] using x.asIdeal.add_mem hf hm
    exact x.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h1 isUnit_one)
  · exact Or.inr hx

/-- The full original second-parameter/Laurent gluing is the entire affine line. -/
def terminalSecondAffineIso : pushout f s ≅ ProjectiveLine.chart K :=
  SchemeOpenPushout.coverIso f s j r
    (terminalSecondAffine_isPullback D k hk b3 b4 b6 h3 h4 h6 hp)
    (terminalSecondAffine_cover b6)

/-- The affine comparison fixes the entire original parameter open. -/
@[reassoc] theorem terminalSecondAffineIso_parameter :
    pushout.inl f s ≫ (terminalSecondAffineIso D k hk b3 b4 b6 h3 h4 h6 hp).hom = j :=
  SchemeOpenPushout.inl_coverIso _ _ _ _ _ _

/-- The affine comparison keeps exactly the inverse terminal Laurent coordinate. -/
@[reassoc] theorem terminalSecondAffineIso_torus :
    pushout.inr f s ≫ (terminalSecondAffineIso D k hk b3 b4 b6 h3 h4 h6 hp).hom = r :=
  SchemeOpenPushout.inr_coverIso _ _ _ _ _ _

end FLT.Mazur.WeierstrassSuccessiveX
