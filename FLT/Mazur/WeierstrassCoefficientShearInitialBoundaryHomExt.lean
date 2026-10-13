/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassIncidenceShearConicBoundary
public import FLT.Mazur.WeierstrassCoefficientShearInitialBoundaryGeometry
public import FLT.Mazur.WeierstrassConicZeroPunctureCover

/-!
# Both signed punctures determine the whole original initial tensor overlap

The full conic boundary is transported through the original initial transition.
No reduced or punctured replacement of the overlap is assumed.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
open scoped TensorProduct LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {R : Type u} [CommRing R] [IsDomain R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {k : ℕ}
  (d : Data W π k) (e : Data W π (k + 1))
  (S : Type u) [Field S] [Algebra R S] (r : S)
  (hs : algebraMap R S (π ^ k) = 0) (hp : algebraMap R S π = 0)
  (h3 : algebraMap R S e.b3 = 0) (h4 : algebraMap R S e.b4 = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
  (g3 : algebraMap R S d.b3 = 0) (g4 : algebraMap R S d.b4 = 0)
  (g6 : algebraMap R S d.b6 = 0)
  (a : Sˣ) (ha : (a : S) = (rootShearCurve (W.map (algebraMap R S)) r).a₁)
local notation "U" => rootShearCurve (W.map (algebraMap R S)) r
local notation "c" => algebraMap R S d.b6
local notation "hu" => Eq.mp (congrArg IsUnit ha) (Units.isUnit a)
local notation "x" => WeierstrassDilatation.x W (π ^ k) d.b3 d.b4 d.b6
local notation "t₀" => t W (π ^ k) d.b3 d.b4 d.b6
local notation "u₀" => coord W (π ^ k) π e.b3 e.b4 e.b6 2
local notation "A" => PrincipalOpenTensor.transitionIso S x t₀
  (overlapEquiv W (π ^ k) d.b3 d.b4 d.b6)
local notation "B" => PrincipalOpenTensor.transitionIso S x u₀ (previousBoundaryEquiv hπ d e)
local notation "E" => tensorShearInitialConicBoundaryIso W (π ^ k)
  d.b3 d.b4 d.b6 S r hs g3 g4 hr
local notation "H" => tensorShearLineToHorizontal W (π ^ k) π
  e.b3 e.b4 e.b6 S r hs hp h3 h4 hr
local notation "ρ₁" => Spec.map (CommRingCat.ofHom
  (PolygonScaledReciprocal.reciprocal a⁻¹).toRingHom)
local notation "ρ₂" => Spec.map (CommRingCat.ofHom
  (PolygonScaledReciprocal.reciprocal (-a)⁻¹).toRingHom)
local notation "b₁" => Spec.map (CommRingCat.ofHom (conicBoundaryFirst U c hu g6).toRingHom)
local notation "b₂" => Spec.map (CommRingCat.ofHom (conicBoundarySecond U c hu g6).toRingHom)

/-- The full initial boundary comparison retains the first signed original puncture. -/
@[reassoc] theorem coefficientShearInitialBoundary_first :
    b₁ ≫ (E).hom ≫ (A).hom = ρ₁ ≫ H 0 (middle_first_root U) ≫ (B).hom := by
  apply (cancel_mono ((A).inv ≫ PrincipalOpenTensor.inclusion S t₀)).mp
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [tensorShearInitialConicBoundaryIso_inclusion, ← Category.assoc]
  have hb : b₁ ≫ PrincipalOpenTransport.inclusion (conicT (U).a₁ c) =
      Spec.map (CommRingCat.ofHom (conicPuncturedFirst U c g6).toRingHom) := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    exact RingHom.ext (conicBoundaryFirst_base U c hu g6)
  rw [hb]
  exact coefficientShearInitialFirstLine_boundary_spec
    hπ d e S r hs hp h3 h4 hr g3 g4 g6 a ha

/-- The opposite puncture retains its negative scale and original root shift. -/
@[reassoc] theorem coefficientShearInitialBoundary_second :
    b₂ ≫ (E).hom ≫ (A).hom =
      ρ₂ ≫ H (-(U).a₁) (middle_second_root U) ≫ (B).hom := by
  apply (cancel_mono ((A).inv ≫ PrincipalOpenTensor.inclusion S t₀)).mp
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [tensorShearInitialConicBoundaryIso_inclusion, ← Category.assoc]
  have hb : b₂ ≫ PrincipalOpenTransport.inclusion (conicT (U).a₁ c) =
      Spec.map (CommRingCat.ofHom (conicPuncturedSecond U c g6).toRingHom) := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    exact RingHom.ext (conicBoundarySecond_base U c hu g6)
  rw [hb]
  exact coefficientShearInitialSecondLine_boundary_spec
    hπ d e S r hs hp h3 h4 hr g3 g4 g6 a ha

include g3 g4 g6 ha in
/-- The two original signed punctures detect maps on the entire original tensor overlap. -/
theorem coefficientShearInitialBoundary_hom_ext {Y : Scheme.{u}}
    (f g : Spec (.of (Localization.Away ((1 : S) ⊗ₜ[R] x))) ⟶ Y)
    (h₁ : (ρ₁ ≫ H 0 (middle_first_root U) ≫ (B).hom) ≫ f =
      (ρ₁ ≫ H 0 (middle_first_root U) ≫ (B).hom) ≫ g)
    (h₂ : (ρ₂ ≫ H (-(U).a₁) (middle_second_root U) ≫ (B).hom) ≫ f =
      (ρ₂ ≫ H (-(U).a₁) (middle_second_root U) ≫ (B).hom) ≫ g) : f = g := by
  apply (cancel_epi ((E).hom ≫ (A).hom)).mp
  apply conicZeroBoundary_hom_ext U c hu g6
  · simp only [Category.assoc]
    simp only [coefficientShearInitialBoundary_first_assoc
      hπ d e S r hs hp h3 h4 hr g3 g4 g6 a ha]
    simpa only [Category.assoc] using h₁
  · simp only [Category.assoc]
    simp only [coefficientShearInitialBoundary_second_assoc
      hπ d e S r hs hp h3 h4 hr g3 g4 g6 a ha]
    simpa only [Category.assoc] using h₂

end FLT.Mazur.WeierstrassDividedDepth
