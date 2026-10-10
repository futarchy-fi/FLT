/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXTerminalFirstAffineChart
public import FLT.Mazur.WeierstrassSuccessiveXTerminalSecondAffineChart

/-!
# The two completed affine charts cover the actual terminal component

Both original parameter neighborhoods and the entire Laurent chart remain
in the cover. Their overlap maps keep the original reciprocal scale.
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
local notation "P" => laurentConicComponent D k hk b3 b4 b6 h3 h4 h6 hp
local notation "l" => laurentConicComponentConic D k hk b3 b4 b6 h3 h4 h6 hp
local notation "r" => laurentConicComponentTorus D k hk b3 b4 b6 h3 h4 h6 hp
local notation "j" => PrincipalOpenTransport.inclusion (conicParameterPolynomial c)
local notation "f" => laurentConicComponentFirstAffine D k hk b3 b4 b6 h3 h4 h6 hp
local notation "g" => laurentConicComponentSecondAffine D k hk b3 b4 b6 h3 h4 h6 hp

/-- The two entire affine charts exhaust the original conic/Laurent gluing. -/
theorem laurentConicComponentAffine_cover (x : P) :
    (∃ y, f y = x) ∨ ∃ z, g z = x := by
  rcases laurentConicComponent_cover D k hk b3 b4 b6 h3 h4 h6 hp x with
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
  exact laurentConicComponentSections_ne D k hk b3 b4 b6 h3 h4 h6 hp

end FLT.Mazur.WeierstrassSuccessiveX
