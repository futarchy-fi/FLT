/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXTerminalFirstAffineGluing
public import FLT.Mazur.WeierstrassSuccessiveXTerminalLaurentMarks

/-!
# The full first affine chart in the original glued terminal component

The completed affine line embeds openly in the actual conic/Laurent gluing.
It keeps the entire first parameter neighborhood, the entire terminal torus,
and the original first attachment as its affine origin.
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
local notation "f" => conicIncidenceFirstParameterMap a c ha hc
local notation "ψ" => residueLaurentConicMap D k hk b3 b4 b6 h3 h4 h6 hp
local notation "s" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom ψ))
local notation "j" => PrincipalOpenTransport.inclusion (conicParameterPolynomial c)
local notation "P" => laurentConicComponent D k hk b3 b4 b6 h3 h4 h6 hp
local notation "l" => laurentConicComponentConic D k hk b3 b4 b6 h3 h4 h6 hp
local notation "r" => laurentConicComponentTorus D k hk b3 b4 b6 h3 h4 h6 hp
local notation "q" => laurentConicComponentFirstParameter D k hk b3 b4 b6 h3 h4 h6 hp
local notation "E" => terminalFirstAffineIso D k hk b3 b4 b6 h3 h4 h6 hp

local instance terminalFirstAffineBoundary_open : IsOpenImmersion
    (Spec.map (CommRingCat.ofHom
      (algebraMap (ConicCoordinate a c) (ConicIncidenceOpen a c)))) :=
  IsOpenImmersion.of_isLocalization (conicT a c)

local instance terminalFirstParameter_open : IsOpenImmersion q :=
  inferInstanceAs (IsOpenImmersion (_ ≫ _ ≫ _))

/-- The actual first parameter neighborhood and torus agree on their entire boundary. -/
@[reassoc] theorem terminalFirstParameter_condition : f ≫ q = s ≫ r := by
  rw [laurentConicComponentFirstParameter, conicIncidenceFirstParameterMap_conic_assoc]
  exact laurentConicComponent_condition D k hk b3 b4 b6 h3 h4 h6 hp

/-- Their full scheme intersection is the original incidence boundary. -/
theorem terminalFirstParameter_isPullback : IsPullback f s q r := by
  apply IsOpenImmersion.isPullback f s q r
    (terminalFirstParameter_condition D k hk b3 b4 b6 h3 h4 h6 hp).symm
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
      (terminalFirstParameter_condition D k hk b3 b4 b6 h3 h4 h6 hp)⟩

/-- The completed first affine chart inside the original terminal component. -/
def laurentConicComponentFirstAffine : ProjectiveLine.chart K ⟶ P :=
  (E).inv ≫ pushout.desc q r
    (terminalFirstParameter_condition D k hk b3 b4 b6 h3 h4 h6 hp)

/-- The affine chart contains the entire original first parameter open, unchanged. -/
@[reassoc] theorem laurentConicComponentFirstAffine_parameter :
    j ≫ laurentConicComponentFirstAffine D k hk b3 b4 b6 h3 h4 h6 hp = q := by
  rw [laurentConicComponentFirstAffine,
    ← terminalFirstAffineIso_parameter D k hk b3 b4 b6 h3 h4 h6 hp,
    Category.assoc, Iso.hom_inv_id_assoc, pushout.inl_desc]

/-- The affine chart contains the full terminal Laurent chart with coordinate c⁻¹*y. -/
@[reassoc] theorem laurentConicComponentFirstAffine_torus :
    ProjectiveLine.scaledOverlapLeft K ((hc).unit)⁻¹ ≫
      laurentConicComponentFirstAffine D k hk b3 b4 b6 h3 h4 h6 hp = r := by
  rw [laurentConicComponentFirstAffine,
    ← terminalFirstAffineIso_torus D k hk b3 b4 b6 h3 h4 h6 hp,
    Category.assoc, Iso.hom_inv_id_assoc, pushout.inr_desc]

instance laurentConicComponentFirstAffine_open :
    IsOpenImmersion (laurentConicComponentFirstAffine D k hk b3 b4 b6 h3 h4 h6 hp) := by
  let _ := SchemeOpenPushout.coverDesc_isOpenImmersion f s q r
    (terminalFirstParameter_isPullback D k hk b3 b4 b6 h3 h4 h6 hp)
  exact inferInstanceAs (IsOpenImmersion (_ ≫ _))

/-- The origin of the full first affine chart is the original first attachment. -/
@[reassoc] theorem laurentConicComponentFirstAffine_origin :
    ProjectiveLine.chartZero K ≫
      laurentConicComponentFirstAffine D k hk b3 b4 b6 h3 h4 h6 hp =
        laurentConicComponentFirstSection D k hk b3 b4 b6 h3 h4 h6 hp := by
  have h : Spec.map (CommRingCat.ofHom (conicParameterOrigin c).toRingHom) ≫ j =
      ProjectiveLine.chartZero K := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext (RingHom.ext (conicParameterOrigin_base c))
  rw [← h, Category.assoc, laurentConicComponentFirstAffine_parameter,
    laurentConicComponentFirstParameter_origin]

end FLT.Mazur.WeierstrassSuccessiveX
