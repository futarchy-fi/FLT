/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PointedCubicAuxiliaryCover
public import FLT.Mazur.AuxiliaryCyclicProductParameter

/-!
# Full auxiliary and original cyclic labels on a pointed cubic chart

The actual etale coefficient cover carries all auxiliary labels together with
the specified cyclic sections. Coprimality proves faithfulness of the product,
and its cyclic evaluations are precisely the original pulled sections.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.GeneralizedEllipticCurve
open WeierstrassIntegralChart UniversalWeierstrass AuxiliaryLevel
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} (W : WeierstrassCurve Γ(S, ⊤)) [W.IsElliptic]
  (h₂ : IsUnit (2 : Γ(S, ⊤))) {n : ℕ} [NeZero n]
  (φ : Multiplicative (ZMod n) →* (𝟙_ (Over S) ⟶ (pointedCubicFamily W).group))
  (hφ : UniversallyDistinctSections.UniversallyDistinct (fun i : ZMod n ↦ φ (.ofAdd i)))
  (h : Nat.Coprime 4 n)

/-- The actual original pointed cubic carrier is separated. -/
local instance : IsSeparated (pointedCubicFamily W).group.hom :=
  inferInstanceAs (IsSeparated (pullback.snd (integralCurveStructure W) S.toSpecΓ))

/-- The cover as a test of the original base scheme. -/
def pointedCubicAuxiliaryBaseTest : pointedCubicAuxiliaryCover W h₂ ⟶ 𝟙_ (Over S) :=
  Over.homMk (pointedCubicAuxiliaryCover W h₂).hom (Category.comp_id _)

/-- All auxiliary and original cyclic labels on the actual etale cover. -/
def pointedCubicCyclicParameter : pointedCubicAuxiliaryCover W h₂ ⟶
    faithfulScheme (pointedCubicFamily W).group (CyclicLabels n) :=
  coprimeParameter (pointedCubicFamily W).group (Labels 4) (Multiplicative (ZMod n))
    (labels_pow 4)
    (fun b ↦ congrArg Multiplicative.ofAdd (ZModModule.char_nsmul_eq_zero n b.toAdd))
    h (pointedCubicAuxiliaryParameter W h₂)
    (pointedCubicAuxiliaryBaseTest W h₂ ≫ cyclicDistinctParameter _ φ hφ)

/-- Every cyclic label is exactly its original section pulled to the auxiliary cover. -/
@[reassoc] theorem pointedCubicCyclicParameter_cyclic (b : Multiplicative (ZMod n)) :
    pointedCubicCyclicParameter W h₂ φ hφ h ≫ faithfulInclusion _ (CyclicLabels n) ≫
      value _ (CyclicLabels n) (1, b) = pointedCubicAuxiliaryBaseTest W h₂ ≫ φ b := by
  rw [pointedCubicCyclicParameter, coprimeParameter_value, coprimeMarking_apply,
    map_one, _root_.one_mul]
  change ((pointedCubicAuxiliaryBaseTest W h₂ ≫ cyclicDistinctParameter _ φ hφ) ≫
    faithfulInclusion _ _) ≫ value _ _ b = _
  rw [Category.assoc, Category.assoc, cyclicDistinctParameter_value]

include h₂ hφ h in
/-- Full faithful label parameters exist on an actual etale surjective cover of the cubic base. -/
theorem exists_pointedCubic_cyclic_auxiliary_cover :
    ∃ (U : Scheme) (g : U ⟶ S), Etale g ∧ Surjective g ∧
      Nonempty (Over.mk g ⟶ faithfulScheme (pointedCubicFamily W).group (CyclicLabels n)) :=
  ⟨(pointedCubicAuxiliaryCover W h₂).left, (pointedCubicAuxiliaryCover W h₂).hom,
    inferInstance, inferInstance, ⟨pointedCubicCyclicParameter W h₂ φ hφ h⟩⟩

end FLT.Mazur.GeneralizedEllipticCurve
