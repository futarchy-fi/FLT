/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassOriginCartier
public import FLT.Mazur.DivisorCanonicalSection

/-!
# Actual divisor sections and their regular numerator coordinates

Evaluation on the original parameter power identifies sections of the dual
origin ideal on its neighborhood with actual regular numerators. The
canonical section has numerator equal to that parameter power.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- Identify the actual parameter ring with the actual neighborhood global sections. -/
def originSectionRingEquiv : OriginNeighborhood W ≃+*
    Γ(Spec (.of (OriginNeighborhood W)), ⊤) :=
  (Scheme.ΓSpecIso (.of (OriginNeighborhood W))).symm.commRingCatIsoToRingEquiv

/-- The original regular parameter as a genuine scheme section. -/
def originParameterSection : Γ(Spec (.of (OriginNeighborhood W)), ⊤) :=
  originSectionRingEquiv W (originCoordinate W 0)

/-- The intrinsic ideal has this exact equation in the actual section ring. -/
theorem originIdealSheaf_section_equation :
    (originNeighborhoodSection W).ker.ideal ⟨⊤, isAffineOpen_top _⟩ =
      Ideal.span {originParameterSection W} := by
  have h := congrArg (Ideal.map (originSectionRingEquiv W).toRingHom)
    (originIdealSheaf_coordinate W)
  change Ideal.map (originSectionRingEquiv W)
    (Ideal.comap (originSectionRingEquiv W)
      ((originNeighborhoodSection W).ker.ideal ⟨⊤, isAffineOpen_top _⟩)) = _ at h
  rw [Ideal.map_comap_of_surjective _ (originSectionRingEquiv W).surjective,
    Ideal.map_span, Set.image_singleton] at h
  exact h

/-- The original parameter remains regular under the actual section-ring identification. -/
theorem originParameterSection_regular : IsRegular (originParameterSection W) :=
  flatRingHom_isRegular (originSectionRingEquiv W).toRingHom
    (.of_bijective (originSectionRingEquiv W).bijective) (originCoordinate_x_regular W)

/-- All powers have their original parameter-power equation in actual global sections. -/
theorem originIdealSheaf_power_section_equation (n : ℕ) :
    ((originNeighborhoodSection W).ker ^ n).ideal ⟨⊤, isAffineOpen_top _⟩ =
      Ideal.span {originParameterSection W ^ n} := by
  change (originNeighborhoodSection W).ker.ideal ⟨⊤, isAffineOpen_top _⟩ ^ n = _
  rw [originIdealSheaf_section_equation, Ideal.span_singleton_pow]

/-- Every original neighborhood ideal power is effective Cartier. -/
theorem originNeighborhood_power_cartier (n : ℕ) :
    FCurve.EffectiveCartier ((originNeighborhoodSection W).ker ^ n) := by
  rw [← originIdealSheaf_power_neighborhood]
  exact (originIdealSheaf_power_effectiveCartier W n).comap_of_isOpenImmersion _

/-- Actual section coordinates for the dual of the original powered origin ideal. -/
def originDivisorSectionsCoordinate (n : ℕ) :
    Γ(FCurve.divisorLineBundle ((originNeighborhoodSection W).ker ^ n)
      (originNeighborhood_power_cartier W n), ⊤) ≃ₗ[Γ(Spec (.of (OriginNeighborhood W)), ⊤)]
      Γ(Spec (.of (OriginNeighborhood W)), ⊤) :=
  (show FCurve.CartierChart ((originNeighborhoodSection W).ker ^ n)
    ⟨⊤, isAffineOpen_top _⟩ from
      ⟨_, (originParameterSection_regular W).pow n,
        originIdealSheaf_power_section_equation W n⟩).divisorSectionsEquiv
          (originNeighborhood_power_cartier W n) ≪≫ₗ
    FCurve.CartierModule.dualEquiv _ _ ((originParameterSection_regular W).pow n)
      (originIdealSheaf_power_section_equation W n)

/-- The actual canonical section has the powered original equation as its coordinate. -/
theorem originDivisorSectionsCoordinate_canonical (n : ℕ) :
    originDivisorSectionsCoordinate W n
      (FCurve.divisorSection (originNeighborhood_power_cartier W n) ⊤) =
      originParameterSection W ^ n := by
  change FCurve.divisorChartEval _ ⟨⊤, isAffineOpen_top _⟩ (FCurve.divisorSection _ ⊤)
    (FCurve.CartierModule.idealEquiv _ _ _ _ 1) = _
  rw [FCurve.divisorSection_eval]
  exact one_mul _

/-- In the original ring, the canonical numerator is precisely the parameter power. -/
theorem originDivisorSectionsCoordinate_canonical_ring (n : ℕ) :
    (originSectionRingEquiv W).symm (originDivisorSectionsCoordinate W n
      (FCurve.divisorSection (originNeighborhood_power_cartier W n) ⊤)) =
      originCoordinate W 0 ^ n := by
  rw [originDivisorSectionsCoordinate_canonical]
  simp [originParameterSection]

end FLT.Mazur.WeierstrassIntegralChart
