/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveShearTerminalFirstAffineGluing
public import FLT.Mazur.WeierstrassSuccessiveShearTerminalLaurentMarks

/-!
# The full first affine chart in the original glued terminal component

The completed affine line embeds openly in the actual conic/Laurent gluing.
It keeps the entire first parameter neighborhood, the entire terminal torus,
and the original first attachment as its affine origin.
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
local notation "f" => conicIncidenceFirstParameterMap a c ha hc
local notation "ψ" => tensorShearTerminalLaurentConicMap W π k b3 b4 b6 S ρ hs hp h3 h4 hr hc u hu
local notation "s" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom ψ))
local notation "j" => PrincipalOpenTransport.inclusion (conicParameterPolynomial c)
local notation "P" => laurentConicComponent W π k b3 b4 b6 S ρ hs hp h3 h4 hr hc u hu
local notation "l" => laurentConicComponentConic W π k b3 b4 b6 S ρ hs hp h3 h4 hr hc u hu
local notation "r" => laurentConicComponentTorus W π k b3 b4 b6 S ρ hs hp h3 h4 hr hc u hu
local notation "q" => laurentConicComponentFirstParameter W π k b3 b4 b6 S ρ hs hp h3 h4 hr hc u hu
local notation "E" => terminalFirstAffineIso W π k b3 b4 b6 S ρ hs hp h3 h4 hr hc u hu

local instance terminalFirstAffineBoundary_open : IsOpenImmersion
    (Spec.map (CommRingCat.ofHom
      (algebraMap (ConicCoordinate a c) (ConicIncidenceOpen a c)))) :=
  IsOpenImmersion.of_isLocalization (conicT a c)

local instance terminalFirstParameter_open : IsOpenImmersion q :=
  inferInstanceAs (IsOpenImmersion (_ ≫ _ ≫ _))

/-- The actual first parameter neighborhood and torus agree on their entire boundary. -/
@[reassoc] theorem terminalFirstParameter_condition : f ≫ q = s ≫ r := by
  rw [laurentConicComponentFirstParameter, conicIncidenceFirstParameterMap_conic_assoc]
  exact laurentConicComponent_condition W π k b3 b4 b6 S ρ hs hp h3 h4 hr hc u hu

/-- Their full scheme intersection is the original incidence boundary. -/
theorem terminalFirstParameter_isPullback : IsPullback f s q r := by
  apply IsOpenImmersion.isPullback f s q r
    (terminalFirstParameter_condition W π k b3 b4 b6 S ρ hs hp h3 h4 hr hc u hu).symm
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
    exact ⟨((conicFirstParameterIso a c ha).inv ≫ conicFirstOpenImmersion a c) y, hy⟩
  · rintro ⟨y, rfl⟩
    exact ⟨f y, congrArg (fun g => g y)
      (terminalFirstParameter_condition W π k b3 b4 b6 S ρ hs hp h3 h4 hr hc u hu)⟩

/-- The completed first affine chart inside the original terminal component. -/
def laurentConicComponentFirstAffine : ProjectiveLine.chart K ⟶ P :=
  (E).inv ≫ pushout.desc q r
    (terminalFirstParameter_condition W π k b3 b4 b6 S ρ hs hp h3 h4 hr hc u hu)

/-- The affine chart contains the entire original first parameter open, unchanged. -/
@[reassoc] theorem laurentConicComponentFirstAffine_parameter :
    j ≫ laurentConicComponentFirstAffine W π k b3 b4 b6 S ρ hs hp h3 h4 hr hc u hu = q := by
  rw [laurentConicComponentFirstAffine,
    ← terminalFirstAffineIso_parameter W π k b3 b4 b6 S ρ hs hp h3 h4 hr hc u hu,
    Category.assoc, Iso.hom_inv_id_assoc, pushout.inl_desc]

/-- The affine chart contains the full terminal Laurent chart with coordinate c⁻¹*y. -/
@[reassoc] theorem laurentConicComponentFirstAffine_torus :
    ProjectiveLine.scaledOverlapLeft K ((hc).unit)⁻¹ ≫
      laurentConicComponentFirstAffine W π k b3 b4 b6 S ρ hs hp h3 h4 hr hc u hu = r := by
  rw [laurentConicComponentFirstAffine,
    ← terminalFirstAffineIso_torus W π k b3 b4 b6 S ρ hs hp h3 h4 hr hc u hu,
    Category.assoc, Iso.hom_inv_id_assoc, pushout.inr_desc]

instance laurentConicComponentFirstAffine_open :
    IsOpenImmersion (laurentConicComponentFirstAffine W π k b3 b4 b6 S ρ hs hp h3 h4 hr hc u hu)
      := by
  let _ := SchemeOpenPushout.coverDesc_isOpenImmersion f s q r
    (terminalFirstParameter_isPullback W π k b3 b4 b6 S ρ hs hp h3 h4 hr hc u hu)
  exact inferInstanceAs (IsOpenImmersion (_ ≫ _))

/-- The origin of the full first affine chart is the original first attachment. -/
@[reassoc] theorem laurentConicComponentFirstAffine_origin :
    ProjectiveLine.chartZero K ≫
      laurentConicComponentFirstAffine W π k b3 b4 b6 S ρ hs hp h3 h4 hr hc u hu =
        laurentConicComponentFirstSection W π k b3 b4 b6 S ρ hs hp h3 h4 hr hc u hu := by
  have h : Spec.map (CommRingCat.ofHom (conicParameterOrigin c).toRingHom) ≫ j =
      ProjectiveLine.chartZero K := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext (RingHom.ext (conicParameterOrigin_base c))
  rw [← h, Category.assoc, laurentConicComponentFirstAffine_parameter,
    laurentConicComponentFirstParameter_origin]

end FLT.Mazur.WeierstrassSuccessiveShearTerminal
