/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveShearTerminalFirstAffineChart
public import FLT.Mazur.WeierstrassSuccessiveShearTerminalSecondAffineChart

/-!
# The two completed affine charts cover the actual terminal component

Both original parameter neighborhoods and the entire Laurent chart remain
in the cover. Their overlap maps keep the original reciprocal scale.
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
local notation "P" => laurentConicComponent W π k b3 b4 b6 S ρ hs hp h3 h4 hr hc u hu
local notation "l" => laurentConicComponentConic W π k b3 b4 b6 S ρ hs hp h3 h4 hr hc u hu
local notation "r" => laurentConicComponentTorus W π k b3 b4 b6 S ρ hs hp h3 h4 hr hc u hu
local notation "j" => PrincipalOpenTransport.inclusion (conicParameterPolynomial c)
local notation "f" => laurentConicComponentFirstAffine W π k b3 b4 b6 S ρ hs hp h3 h4 hr hc u hu
local notation "g" => laurentConicComponentSecondAffine W π k b3 b4 b6 S ρ hs hp h3 h4 hr hc u hu

/-- The two entire affine charts exhaust the original conic/Laurent gluing. -/
theorem laurentConicComponentAffine_cover (x : P) :
    (∃ y, f y = x) ∨ ∃ z, g z = x := by
  rcases laurentConicComponent_cover W π k b3 b4 b6 S ρ hs hp h3 h4 hr hc u hu x with
    ⟨z, rfl⟩ | ⟨z, rfl⟩
  · rcases conicOpenImmersions_cover a c ha z with ⟨y, rfl⟩ | ⟨y, rfl⟩
    · left
      refine ⟨j ((conicFirstParameterIso a c ha).hom y), ?_⟩
      rw [← Scheme.Hom.comp_apply, laurentConicComponentFirstAffine_parameter]
      change ((conicFirstParameterIso a c ha).hom ≫
        (conicFirstParameterIso a c ha).inv ≫ conicFirstOpenImmersion a c ≫ l) y = _
      rw [Iso.hom_inv_id_assoc]
      rfl
    · right
      refine ⟨j ((conicSecondParameterIso a c ha).hom y), ?_⟩
      rw [← Scheme.Hom.comp_apply, laurentConicComponentSecondAffine_parameter]
      change ((conicSecondParameterIso a c ha).hom ≫
        (conicSecondParameterIso a c ha).inv ≫ conicSecondOpenImmersion a c ≫ l) y = _
      rw [Iso.hom_inv_id_assoc]
      rfl
  · right
    refine ⟨ProjectiveLine.overlapRight K z, ?_⟩
    rw [← Scheme.Hom.comp_apply, laurentConicComponentSecondAffine_torus]

/-- The complete affine charts keep the original ordered Laurent transition. -/
@[reassoc] theorem laurentConicComponentAffine_transition :
    ProjectiveLine.scaledOverlapLeft K ((hc).unit)⁻¹ ≫ f =
      ProjectiveLine.overlapRight K ≫ g := by
  rw [laurentConicComponentFirstAffine_torus, laurentConicComponentSecondAffine_torus]

/-- The two affine origins are still the distinct original ordered attachments. -/
theorem laurentConicComponentAffine_origins_ne :
    ProjectiveLine.chartZero K ≫ f ≠ ProjectiveLine.chartZero K ≫ g := by
  rw [laurentConicComponentFirstAffine_origin, laurentConicComponentSecondAffine_origin]
  exact laurentConicComponentSections_ne W π k b3 b4 b6 S ρ hs hp h3 h4 hr hc u hu

end FLT.Mazur.WeierstrassSuccessiveShearTerminal
