/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearAdjacentTransition

/-!
# Full signed intersections of the adjacent conic boundary and tangent lines

Transport the entire conic incidence open to the next horizontal open through
the genuine integral transitions. Each signed Laurent puncture is its full
scheme intersection with the corresponding actual tangent line.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {k : ℕ}
  (d : Data W π (k + 1)) (e : Data W π (k + 1 + 1))
  (S : Type u) [CommRing S] [Algebra R S] (r : S)
  (hs : algebraMap R S (π ^ k) = 0) (hp : algebraMap R S π = 0)
  (h3 : algebraMap R S e.b3 = 0) (h4 : algebraMap R S e.b4 = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
local notation "U" => rootShearCurve (W.map (algebraMap R S)) r
local notation "hsNext" => coefficientShearAdjacent_scale S hp (k := k)
local notation "g3" => And.left (coefficientShearAdjacent_coefficients hπ d e S hp)
local notation "g4" => And.left (And.right (coefficientShearAdjacent_coefficients hπ d e S hp))
local notation "gc" => And.right (And.right (coefficientShearAdjacent_coefficients hπ d e S hp))
local notation "c" => algebraMap R S d.b6
local notation "φ" => tensorShearDividedConicOpenEquiv W (π ^ k) π
  d.b3 d.b4 d.b6 S r hs hp g3 g4 hr
local notation "E" => tensorAdjacentBoundaryEquiv hπ d e S
local notation "H" => Localization.Away (tensorCoord W (π ^ (k + 1)) π e.b3 e.b4 e.b6 S 2)
local notation "B" => MiddleConicOpen U c
local notation "i" => PrincipalOpenTensor.inclusion S (coord W (π ^ (k + 1)) π e.b3 e.b4 e.b6 2)
local notation "p" => Spec.map (CommRingCat.ofHom
  (Polynomial.toLaurent : Polynomial S →+* S[T;T⁻¹]))

/-- The actual conic open identifies the next horizontal open by both original transitions. -/
def coefficientShearAdjacentConicIso : Spec (.of B) ≅ Spec (.of H) :=
  Scheme.Spec.mapIso ((E).symm.trans φ).toRingEquiv.toCommRingCatIso.op

local notation "J" => coefficientShearAdjacentConicIso hπ d e S r hs hp hr
variable (a : Sˣ) (ha : (a : S) = (rootShearCurve (W.map (algebraMap R S)) r).a₁)
local notation "hu" => Eq.mp (congrArg IsUnit ha) (Units.isUnit a)
local notation "b₁" => Spec.map
  (CommRingCat.ofHom (AlgHom.toRingHom (conicBoundaryFirst U c hu gc)))
local notation "b₂" => Spec.map
  (CommRingCat.ofHom (AlgHom.toRingHom (conicBoundarySecond U c hu gc)))
local notation "ρ₁" => Scheme.Spec.mapIso
  (Iso.op (RingEquiv.toCommRingCatIso
    (AlgEquiv.toRingEquiv (PolygonScaledReciprocal.equiv (a⁻¹)))))
local notation "ρ₂" => Scheme.Spec.mapIso
  (Iso.op (RingEquiv.toCommRingCatIso
    (AlgEquiv.toRingEquiv (PolygonScaledReciprocal.equiv ((-a)⁻¹)))))
local notation "l₁" => tensorShearLineToHorizontal W (π ^ (k + 1)) π
  e.b3 e.b4 e.b6 S r hsNext hp h3 h4 hr 0 (middle_first_root U)
local notation "l₂" => tensorShearLineToHorizontal W (π ^ (k + 1)) π
  e.b3 e.b4 e.b6 S r hsNext hp h3 h4 hr
  (-WeierstrassCurve.a₁ U) (middle_second_root U)
local notation "L₁" => Spec.map (CommRingCat.ofHom
  (AlgHom.toRingHom (tensorShearLineMap W (π ^ (k + 1)) π e.b3 e.b4 e.b6 S r hsNext hp h3 h4 hr
    0 (middle_first_root U))))
local notation "L₂" => Spec.map (CommRingCat.ofHom
  (AlgHom.toRingHom (tensorShearLineMap W (π ^ (k + 1)) π e.b3 e.b4 e.b6 S r hsNext hp h3 h4 hr
    (-WeierstrassCurve.a₁ U) (middle_second_root U))))

/-- The first signed puncture preserves the actual original horizontal transition. -/
@[reassoc] theorem coefficientShearAdjacentFirst_square : b₁ ≫ (J).hom = (ρ₁).hom ≫ l₁ := by
  rw [← tensorShearLineOpenMap_spec]
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  change conicBoundaryFirst U c hu gc (φ ((E).symm z)) =
    PolygonScaledReciprocal.reciprocal a⁻¹
      (tensorShearLineOpenMap W (π ^ (k + 1)) π e.b3 e.b4 e.b6
        S r hsNext hp h3 h4 hr 0 (middle_first_root U) z)
  have hz := DFunLike.congr_fun
    (coefficientShearAdjacentFirst_transition hπ d e S r hs hp h3 h4 hr a ha) ((E).symm z)
  simpa only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply] using hz

/-- The opposite signed puncture preserves the same transition and its negative scale. -/
@[reassoc] theorem coefficientShearAdjacentSecond_square : b₂ ≫ (J).hom = (ρ₂).hom ≫ l₂ := by
  rw [← tensorShearLineOpenMap_spec]
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  change conicBoundarySecond U c hu gc (φ ((E).symm z)) =
    PolygonScaledReciprocal.reciprocal (-a)⁻¹
      (tensorShearLineOpenMap W (π ^ (k + 1)) π e.b3 e.b4 e.b6
        S r hsNext hp h3 h4 hr (-(U).a₁) (middle_second_root U) z)
  have hz := DFunLike.congr_fun
    (coefficientShearAdjacentSecond_transition hπ d e S r hs hp h3 h4 hr a ha) ((E).symm z)
  simpa only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply] using hz

/-- The first entire punctured line is the full scheme intersection with the conic open. -/
theorem coefficientShearAdjacentFirst_isPullback :
    IsPullback b₁ ((ρ₁).hom ≫ p) ((J).hom ≫ i) L₁ := by
  have sq : IsPullback b₁ (ρ₁).hom (J).hom l₁ :=
    IsPullback.of_vert_isIso
      ⟨coefficientShearAdjacentFirst_square hπ d e S r hs hp h3 h4 hr a ha⟩
  exact sq.paste_vert (tensorShearLineHorizontal_isPullback W (π ^ (k + 1)) π
    e.b3 e.b4 e.b6 S r hsNext hp h3 h4 hr 0 (middle_first_root U))

/-- The second entire punctured line has the full signed intersection as well. -/
theorem coefficientShearAdjacentSecond_isPullback :
    IsPullback b₂ ((ρ₂).hom ≫ p) ((J).hom ≫ i) L₂ := by
  have sq : IsPullback b₂ (ρ₂).hom (J).hom l₂ :=
    IsPullback.of_vert_isIso
      ⟨coefficientShearAdjacentSecond_square hπ d e S r hs hp h3 h4 hr a ha⟩
  exact sq.paste_vert (tensorShearLineHorizontal_isPullback W (π ^ (k + 1)) π
    e.b3 e.b4 e.b6 S r hsNext hp h3 h4 hr (-(U).a₁) (middle_second_root U))

end FLT.Mazur.WeierstrassDividedDepth
