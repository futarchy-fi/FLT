/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXConicBoundaryCharts
public import FLT.Mazur.WeierstrassSuccessiveShearTerminalLaurentOpen
public import FLT.Mazur.ProjectiveLineScaledAffineOverlap
public import FLT.Mazur.SchemeOpenPushoutCoverIso

/-!
# Completing the original first conic parameter to the full affine line

The first parameter retains the original scale: z₁=c⁻¹*y. The full
parameter open and the entire scaled Laurent torus glue to its affine line.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open scoped Polynomial LaurentPolynomial TensorProduct
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
local notation "f" => conicIncidenceFirstParameterMap a c ha hc
local notation "ψ" => tensorShearTerminalLaurentConicMap W π k b3 b4 b6 S ρ hs hp h3 h4 hr hc u hu
local notation "s" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom ψ))
local notation "j" => PrincipalOpenTransport.inclusion (conicParameterPolynomial c)
local notation "r" => ProjectiveLine.scaledOverlapLeft K (Inv.inv (IsUnit.unit hc))
local notation "tx" => (1 : S) ⊗ₜ[R] WeierstrassDilatation.x W (π ^ (k + 1)) b3 b4 b6
local notation "e" => tensorShearTerminalLaurentEquiv W π k b3 b4 b6 S ρ hp h3 h4 hr hc u hu
local notation "C" => LaurentPolynomial.C (R := K)
local notation "Y" => (LaurentPolynomial.T 1 : K[T;T⁻¹])
local notation "I" => (LaurentPolynomial.T (-1) : K[T;T⁻¹])
local notation "A" => C (Units.val (Inv.inv (u)))
local notation "V" => C (Units.val (Inv.inv (IsUnit.unit hc)))

/-- The actual boundary map retains the scaled first affine coordinate. -/
@[reassoc] theorem terminalFirstAffine_condition : f ≫ j = s ≫ r := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply Polynomial.ringHom_ext
  · intro q
    change conicIncidenceFirstParameterHom a c ha hc (algebraMap K _ q) =
      ψ (Polynomial.toLaurent (PolygonChartScaling.affine ((hc).unit)⁻¹ (Polynomial.C q)))
    rw [AlgHom.commutes, PolygonChartScaling.affine_C, Polynomial.toLaurent_C]
    exact ((ψ).commutes q).symm
  · change conicIncidenceFirstParameterHom a c ha hc (conicParameterZ c) =
      ψ (Polynomial.toLaurent (PolygonChartScaling.affine ((hc).unit)⁻¹ Polynomial.X))
    rw [conicIncidenceFirstParameterHom_z, PolygonChartScaling.affine_X, map_mul,
      Polynomial.toLaurent_C, Polynomial.toLaurent_X, map_mul,
      tensorShearTerminalLaurentConicMap_firstParameter]
    have hcoeff : ψ (C (↑((hc).unit)⁻¹ : K)) =
        algebraMap K (ConicIncidenceOpen a c) (↑((hc).unit)⁻¹ : K) := (ψ).commutes _
    rw [hcoeff]
    change _ = algebraMap K (ConicIncidenceOpen a c) (↑((hc).unit)⁻¹ : K) *
      (algebraMap K (ConicIncidenceOpen a c) c * _)
    have hci : (↑((hc).unit)⁻¹ : K) * c = 1 := by
      simpa only [(hc).unit_spec] using Units.inv_mul (hc).unit
    rw [← mul_assoc, ← map_mul, hci, map_one, one_mul]

/-- The horizontal denominator differs from the scaled first denominator by a unit. -/
theorem terminalFirstAffine_denominator : (e) tx =
    (A * C c * I) * Polynomial.toLaurent
      (PolygonChartScaling.affine ((hc).unit)⁻¹ (conicParameterPolynomial c)) := by
  rw [tensorShearTerminalLaurent_x]
  simp only [conicParameterPolynomial, map_sub, map_one, map_mul, map_pow,
    PolygonChartScaling.affine_C, PolygonChartScaling.affine_X,
    Polynomial.toLaurent_C, Polynomial.toLaurent_X]
  have hci : C c * V = 1 := by
    have hcv : c * (↑((hc).unit)⁻¹ : K) = 1 := by
      simpa only [(hc).unit_spec] using Units.mul_inv (hc).unit
    rw [← map_mul, hcv, map_one]
  have hiy : I * Y = 1 := by
    rw [← LaurentPolynomial.T_add]
    rfl
  have h : (C c * I) * (C c * (V * Y) ^ 2) = Y := by
    calc (C c * I) * (C c * (V * Y) ^ 2) = (C c * V) ^ 2 * (I * Y) * Y := by ring
      _ = Y := by rw [hci, hiy]; simp only [one_pow, one_mul]
  calc A * (C c * I - Y) = A * (C c * I - (C c * I) * (C c * (V * Y) ^ 2)) := by
        rw [h]
    _ = _ := by ring

/-- The whole original incidence open is the exact first affine-chart intersection. -/
theorem terminalFirstAffine_isPullback : IsPullback f s j r := by
  apply IsOpenImmersion.isPullback f s j r
    (terminalFirstAffine_condition W π k b3 b4 b6 S ρ hs hp h3 h4 hr hc u hu).symm
  apply TopologicalSpace.Opens.ext
  change r ⁻¹' Set.range j = Set.range s
  rw [show Set.range j =
    (PrimeSpectrum.basicOpen (conicParameterPolynomial c) : Set (PrimeSpectrum K[X])) from
      PrimeSpectrum.localization_away_comap_range _ _, tensorShearTerminalLaurentConicMap_range]
  ext q
  change Polynomial.toLaurent
    (PolygonChartScaling.affine ((hc).unit)⁻¹ (conicParameterPolynomial c)) ∉ q.asIdeal ↔
      (e) tx ∉ q.asIdeal
  rw [terminalFirstAffine_denominator]
  exact (not_congr (q.asIdeal.unit_mul_mem_iff_mem
    ((((u)⁻¹).isUnit.map C).mul
      ((hc).map C) |>.mul (LaurentPolynomial.isUnit_T (-1))))).symm

/-- The original first-parameter/Laurent gluing is the full first affine line. -/
def terminalFirstAffineIso : pushout f s ≅ ProjectiveLine.chart K :=
  SchemeOpenPushout.coverIso f s j r
    (terminalFirstAffine_isPullback W π k b3 b4 b6 S ρ hs hp h3 h4 hr hc u hu)
    (ProjectiveLine.conicParameter_scaledTorus_cover K c ((hc).unit)⁻¹)

/-- The first affine completion keeps the full original first parameter neighborhood. -/
@[reassoc] theorem terminalFirstAffineIso_parameter :
    pushout.inl f s ≫ (terminalFirstAffineIso W π k b3 b4 b6 S ρ hs hp h3 h4 hr hc u hu).hom = j :=
  SchemeOpenPushout.inl_coverIso _ _ _ _ _ _

/-- The first affine completion retains z₁=c⁻¹*y on the entire terminal torus. -/
@[reassoc] theorem terminalFirstAffineIso_torus :
    pushout.inr f s ≫ (terminalFirstAffineIso W π k b3 b4 b6 S ρ hs hp h3 h4 hr hc u hu).hom = r :=
  SchemeOpenPushout.inr_coverIso _ _ _ _ _ _

end FLT.Mazur.WeierstrassSuccessiveShearTerminal
