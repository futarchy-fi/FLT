/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassOriginalAuxiliaryCover
public import FLT.Mazur.AuxiliaryCyclicProductParameter

/-!
# Full auxiliary labels retaining an original cyclic marking

The actual etale auxiliary cover of the original cubic carries a faithful
product marking. Its cyclic factor consists exactly of the pullbacks of the
specified original cyclic sections, with no field or reducedness assumption.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.UniversalWeierstrass
open WeierstrassIntegralChart AuxiliaryLevel
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] (W : WeierstrassCurve R)
  (h₂ : IsUnit (2 : R)) (hΔ : IsUnit W.Δ)
  {n : ℕ} [NeZero n]
  (φ : Multiplicative (ZMod n) →* (𝟙_ (Over (Spec (.of R))) ⟶ (integralCurveGroup W hΔ).X))
  (hφ : UniversallyDistinctSections.UniversallyDistinct
    (fun i : ZMod n ↦ φ (Multiplicative.ofAdd i)))
  (h : Nat.Coprime 4 n)

/-- The actual structure map from the auxiliary cover to the original base test. -/
def originalAuxiliaryBaseTest : originalAuxiliaryCover W h₂ hΔ ⟶
    𝟙_ (Over (Spec (.of R))) :=
  Over.homMk (originalAuxiliaryCover W h₂ hΔ).hom (Category.comp_id _)

/-- The full product parameter on the original cubic, retaining its specified cyclic marking. -/
def originalCyclicAuxiliaryParameter : originalAuxiliaryCover W h₂ hΔ ⟶
    faithfulScheme (integralCurveGroup W hΔ).X (CyclicLabels n) :=
  coprimeParameter (integralCurveGroup W hΔ).X (Labels 4) (Multiplicative (ZMod n))
    (labels_pow 4)
    (fun b ↦ congrArg Multiplicative.ofAdd (ZModModule.char_nsmul_eq_zero n b.toAdd))
    h (originalAuxiliaryParameter W h₂ hΔ)
    (originalAuxiliaryBaseTest W h₂ hΔ ≫ cyclicDistinctParameter _ φ hφ)

/-- Every cyclic label in the full parameter is its original section pulled to the actual cover. -/
@[reassoc] theorem originalCyclicAuxiliaryParameter_cyclic (b : Multiplicative (ZMod n)) :
    originalCyclicAuxiliaryParameter W h₂ hΔ φ hφ h ≫
      faithfulInclusion (integralCurveGroup W hΔ).X (CyclicLabels n) ≫
      value (integralCurveGroup W hΔ).X (CyclicLabels n) (1, b) =
        originalAuxiliaryBaseTest W h₂ hΔ ≫ φ b := by
  rw [originalCyclicAuxiliaryParameter, coprimeParameter_value, coprimeMarking_apply,
    map_one, _root_.one_mul]
  change ((originalAuxiliaryBaseTest W h₂ hΔ ≫ cyclicDistinctParameter _ φ hφ) ≫
    faithfulInclusion _ _) ≫ value _ _ b = _
  rw [Category.assoc, Category.assoc, cyclicDistinctParameter_value]

include h₂ hφ h in
/-- Full auxiliary and original cyclic labels exist etale locally on the original cubic. -/
theorem exists_original_cyclic_auxiliary_cover :
    ∃ (U : Scheme) (g : U ⟶ Spec (.of R)), Etale g ∧ Surjective g ∧
      Nonempty (Over.mk g ⟶ faithfulScheme (integralCurveGroup W hΔ).X (CyclicLabels n)) :=
  ⟨(originalAuxiliaryCover W h₂ hΔ).left, (originalAuxiliaryCover W h₂ hΔ).hom,
    inferInstance, inferInstance, ⟨originalCyclicAuxiliaryParameter W h₂ hΔ φ hφ h⟩⟩

end FLT.Mazur.UniversalWeierstrass
