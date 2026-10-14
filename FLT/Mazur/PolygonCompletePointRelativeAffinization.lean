/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointRelativeCoordinateRing
public import FLT.Mazur.SchemeAffinizationUniversal

/-!
# The original affine cubic is the affinization of the marking complement

Every map from the complement to an affine scheme factors uniquely through the
actual coordinate evaluation. The omitted components need not be affine.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "s" => completeBaseMarking K n h i
local notation "U" => Scheme.Opens.toScheme
  (GlobalIdealPowerCompatibility.complement (Scheme.Hom.ker (s)))
local notation "W" => completePointWeierstrassCurve K n h i
local notation "c" => completePointToAffineCubic K n h i

/-- The cubic's affine chart is the spectrum of all original complement functions. -/
def completePointComplementSpectrumIso :
    Spec Γ(U, ⊤) ≅ Spec (.of (W).toAffine.CoordinateRing) := by
  let _ : IsIso (CommRingCat.ofHom (completePointCoordinateEvaluation K n h i)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      ⟨completePointCoordinateEvaluation_injective K n h i,
        completePointCoordinateEvaluation_surjective K n h i⟩
  exact asIso (Spec.map (CommRingCat.ofHom (completePointCoordinateEvaluation K n h i)))

/-- The original coordinate morphism is exactly the canonical map to the section spectrum. -/
@[reassoc] theorem completePointComplementSpectrumIso_fac :
    (U).toSpecΓ ≫ (completePointComplementSpectrumIso K n h i).hom = c := rfl

/-- The actual relative affine cubic has the universal property of the complement's spectrum. -/
theorem completePointToAffineCubic_existsUnique_factor (T : Scheme) [IsAffine T]
    (q : U ⟶ T) : ∃! b : Spec (.of (W).toAffine.CoordinateRing) ⟶ T, c ≫ b = q := by
  let e := completePointComplementSpectrumIso K n h i
  obtain ⟨b, hb, hu⟩ := toSpecΓ_existsUnique_factor U T q
  refine ⟨e.inv ≫ b, ?_, ?_⟩
  · dsimp only
    rw [← completePointComplementSpectrumIso_fac, Category.assoc,
      Iso.hom_inv_id_assoc]
    exact hb
  · intro d hd
    have he : e.hom ≫ d = b := hu _ (by
      dsimp only
      rw [← Category.assoc, completePointComplementSpectrumIso_fac]
      exact hd)
    rw [← he, Iso.inv_hom_id_assoc]

end FLT.Mazur.PolygonInfinitesimalStages
