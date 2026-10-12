/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveShearTerminalSecondAffineGluing
public import FLT.Mazur.WeierstrassSuccessiveShearTerminalLaurentMarks

/-!
# The full second affine chart in the original glued terminal component

The completed affine line embeds openly in the actual conic/Laurent gluing.
It keeps the entire second parameter neighborhood, the entire terminal torus,
and the original second attachment as its affine origin.
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
local notation "P" => laurentConicComponent W π k b3 b4 b6 S ρ hs hp h3 h4 hr hc u hu
local notation "l" => laurentConicComponentConic W π k b3 b4 b6 S ρ hs hp h3 h4 hr hc u hu
local notation "r" => laurentConicComponentTorus W π k b3 b4 b6 S ρ hs hp h3 h4 hr hc u hu
local notation "q" => laurentConicComponentSecondParameter W π k b3 b4 b6 S ρ hs hp h3 h4 hr hc u hu
local notation "E" => terminalSecondAffineIso W π k b3 b4 b6 S ρ hs hp h3 h4 hr hc u hu

local instance terminalSecondAffineBoundary_open : IsOpenImmersion
    (Spec.map (CommRingCat.ofHom
      (algebraMap (ConicCoordinate a c) (ConicIncidenceOpen a c)))) :=
  IsOpenImmersion.of_isLocalization (conicT a c)

local instance terminalSecondParameter_open : IsOpenImmersion q :=
  inferInstanceAs (IsOpenImmersion (_ ≫ _ ≫ _))

/-- The actual second parameter neighborhood and torus agree on their entire boundary. -/
@[reassoc] theorem terminalSecondParameter_condition : f ≫ q = s ≫ r := by
  rw [laurentConicComponentSecondParameter, conicIncidenceSecondParameterMap_conic_assoc]
  exact laurentConicComponent_condition W π k b3 b4 b6 S ρ hs hp h3 h4 hr hc u hu

/-- Their full scheme intersection is the original incidence boundary. -/
theorem terminalSecondParameter_isPullback : IsPullback f s q r := by
  apply IsOpenImmersion.isPullback f s q r
    (terminalSecondParameter_condition W π k b3 b4 b6 S ρ hs hp h3 h4 hr hc u hu).symm
  apply TopologicalSpace.Opens.ext
  change r ⁻¹' Set.range q = Set.range s
  have h := SchemeOpenPushout.inr_preimage_inl
    (Spec.map (CommRingCat.ofHom
      (algebraMap (ConicCoordinate a c) (ConicIncidenceOpen a c)))) s
  change r ⁻¹' Set.range l = Set.range s at h
  ext x
  constructor
  · rintro ⟨y, hy⟩
    rw [← h]
    exact ⟨((conicSecondParameterIso a c ha).inv ≫ conicSecondOpenImmersion a c) y, hy⟩
  · rintro ⟨y, rfl⟩
    exact ⟨f y, congrArg (fun g => g y)
      (terminalSecondParameter_condition W π k b3 b4 b6 S ρ hs hp h3 h4 hr hc u hu)⟩

/-- The completed second affine chart inside the original terminal component. -/
def laurentConicComponentSecondAffine : ProjectiveLine.chart K ⟶ P :=
  (E).inv ≫ pushout.desc q r
    (terminalSecondParameter_condition W π k b3 b4 b6 S ρ hs hp h3 h4 hr hc u hu)

/-- The affine chart contains the entire original second parameter open, unchanged. -/
@[reassoc] theorem laurentConicComponentSecondAffine_parameter :
    j ≫ laurentConicComponentSecondAffine W π k b3 b4 b6 S ρ hs hp h3 h4 hr hc u hu = q := by
  rw [laurentConicComponentSecondAffine,
    ← terminalSecondAffineIso_parameter W π k b3 b4 b6 S ρ hs hp h3 h4 hr hc u hu,
    Category.assoc, Iso.hom_inv_id_assoc, pushout.inl_desc]

/-- The affine chart contains the full terminal Laurent chart with coordinate y⁻¹. -/
@[reassoc] theorem laurentConicComponentSecondAffine_torus :
    ProjectiveLine.overlapRight K ≫
      laurentConicComponentSecondAffine W π k b3 b4 b6 S ρ hs hp h3 h4 hr hc u hu = r := by
  rw [laurentConicComponentSecondAffine,
    ← terminalSecondAffineIso_torus W π k b3 b4 b6 S ρ hs hp h3 h4 hr hc u hu,
    Category.assoc, Iso.hom_inv_id_assoc, pushout.inr_desc]

instance laurentConicComponentSecondAffine_open :
    IsOpenImmersion (laurentConicComponentSecondAffine W π k b3 b4 b6 S ρ hs hp h3 h4 hr hc u
      hu) := by
  let _ := SchemeOpenPushout.coverDesc_isOpenImmersion f s q r
    (terminalSecondParameter_isPullback W π k b3 b4 b6 S ρ hs hp h3 h4 hr hc u hu)
  exact inferInstanceAs (IsOpenImmersion (_ ≫ _))

/-- The origin of the full second affine chart is the original second attachment. -/
@[reassoc] theorem laurentConicComponentSecondAffine_origin :
    ProjectiveLine.chartZero K ≫
      laurentConicComponentSecondAffine W π k b3 b4 b6 S ρ hs hp h3 h4 hr hc u hu =
        laurentConicComponentSecondSection W π k b3 b4 b6 S ρ hs hp h3 h4 hr hc u hu := by
  have h : Spec.map (CommRingCat.ofHom (conicParameterOrigin c).toRingHom) ≫ j =
      ProjectiveLine.chartZero K := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext (RingHom.ext (conicParameterOrigin_base c))
  rw [← h, Category.assoc, laurentConicComponentSecondAffine_parameter,
    laurentConicComponentSecondParameter_origin]

end FLT.Mazur.WeierstrassSuccessiveShearTerminal
