/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXConicBoundaryCharts
public import FLT.Mazur.WeierstrassSuccessiveShearTerminalLaurentOpen
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
namespace FLT.Mazur.WeierstrassSuccessiveShearTerminal
open WeierstrassModificationX WeierstrassSuccessiveX WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (π : R)
  (k : ℕ) (b3 b4 b6 : R) (S : Type u) [Field S] [Algebra R S] (ρ : S)
  (hs : algebraMap R S (π ^ k) = 0) (hp : algebraMap R S π = 0)
  (h3 : algebraMap R S b3 = 0) (h4 : algebraMap R S b4 = 0)
  (hr : ρ ^ 2 + algebraMap R S W.a₁ * ρ - algebraMap R S W.a₂ = 0)
  (hc : IsUnit (algebraMap R S b6)) (u : Sˣ)
  (hu : (u : S) = (rootShearCurve (W.map (algebraMap R S)) ρ).a₁)
local notation "U" => rootShearCurve (W.map (algebraMap R S)) ρ
local notation "K" => S
local notation "a" => WeierstrassCurve.a₁ U
local notation "c" => algebraMap R S b6
local notation "ha" => Eq.mp (congrArg IsUnit hu) (Units.isUnit u)
local notation "f" => conicIncidenceSecondParameterMap a c ha hc
local notation "ψ" => tensorShearTerminalLaurentConicMap W π k b3 b4 b6 S ρ hs hp h3 h4 hr hc u hu
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
    exact (tensorShearTerminalLaurentConicMap_inverseParameter W π k b3 b4 b6 S ρ hs hp h3 h4 hr
      hc u hu).symm

/-- The original finite-model boundary is the complete affine-chart intersection. -/
theorem terminalSecondAffine_isPullback : IsPullback f s j r := by
  apply IsOpenImmersion.isPullback f s j r
    (terminalSecondAffine_condition W π k b3 b4 b6 S ρ hs hp h3 h4 hr hc u hu).symm
  apply TopologicalSpace.Opens.ext
  change r ⁻¹' Set.range j = Set.range s
  rw [show Set.range j =
    (PrimeSpectrum.basicOpen (conicParameterPolynomial c) : Set (PrimeSpectrum K[X])) from
      PrimeSpectrum.localization_away_comap_range _ _]
  exact (tensorShearTerminalLaurentConicMap_range_inverseParameter W π k b3 b4 b6 S ρ hs hp h3
    h4 hr hc u hu).symm

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
    (terminalSecondAffine_isPullback W π k b3 b4 b6 S ρ hs hp h3 h4 hr hc u hu)
    (terminalSecondAffine_cover b6 S)

/-- The affine comparison fixes the entire original parameter open. -/
@[reassoc] theorem terminalSecondAffineIso_parameter :
    pushout.inl f s ≫ (terminalSecondAffineIso W π k b3 b4 b6 S ρ hs hp h3 h4 hr hc u hu).hom = j :=
  SchemeOpenPushout.inl_coverIso _ _ _ _ _ _

/-- The affine comparison keeps exactly the inverse terminal Laurent coordinate. -/
@[reassoc] theorem terminalSecondAffineIso_torus :
    pushout.inr f s ≫ (terminalSecondAffineIso W π k b3 b4 b6 S ρ hs hp h3 h4 hr hc u hu).hom = r :=
  SchemeOpenPushout.inr_coverIso _ _ _ _ _ _

end FLT.Mazur.WeierstrassSuccessiveShearTerminal
