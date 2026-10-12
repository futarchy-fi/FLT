/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveSectionComposition
public import FLT.Mazur.GeneralizedCurveSmoothBaseCubic

/-!
# Original local pointed cubic maps on the smooth base locus

The local neighborhood maps directly to the original base, and its curve is
the original single base change. The full DR comparison flattens the intermediate
smooth-base restriction while preserving the actual marking and coefficient map.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.GeneralizedEllipticCurve
open FCurve WeierstrassIntegralChart GroupSectionBaseChange
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {S : Scheme.{0}} (E : GeneralizedEllipticCurve S) [IsLocallyNoetherian S]

/-- Every smooth base point has an affine pointed cubic chart on its original direct base change. -/
theorem exists_original_local_pointedCubic
    (s : 𝟙_ (Over S) ⟶ E.curve) {V : S.Opens} {x : S}
    (hx : x ∈ smoothBaseOpen E) (hxV : x ∈ V) :
    ∃ (T : Scheme) (_ : IsAffine T) (g : T ⟶ S),
      IsOpenImmersion g ∧ x ∈ Set.range g ∧ Set.range g ⊆ V ∧
        ∃ (W : WeierstrassCurve Γ(T, ⊤)), W.IsElliptic ∧
          ∃ e : (E.baseChange g).curve.left ≅ integralCurve W,
            e.hom ≫ integralCurveStructure W = (E.baseChange g).curve.hom ≫ T.toSpecΓ ∧
              (pullSection g s).left ≫ e.hom = T.toSpecΓ ≫ integralCurveZero W := by
  let B := smoothBaseOpen E
  obtain ⟨U, hxU, hUV, W, hW, e, he, hs⟩ :=
    exists_smoothBase_local_pointedCubic E s (x := (⟨x, hx⟩ : B.toScheme))
      (V := B.ι ⁻¹ᵁ V) hxV
  let g : U.1.toScheme ⟶ S := U.1.ι ≫ B.ι
  let c := ((forgetCurve (S := U.1.toScheme)) ⋙ Over.forget U.1.toScheme).mapIso
    (E.baseChangeCompIso B.ι U.1.ι)
  refine ⟨U.1.toScheme, U.2, g, inferInstance, ?_, ?_, W, hW, c ≪≫ e, ?_, ?_⟩
  · exact ⟨⟨⟨x, hx⟩, hxU⟩, rfl⟩
  · rintro _ ⟨y, rfl⟩
    exact hUV y.property
  · change c.hom ≫ e.hom ≫ integralCurveStructure W = _
    rw [he, ← Category.assoc]
    exact congrArg (fun k ↦ k ≫ U.1.toScheme.toSpecΓ)
      (E.baseChangeCompIso B.ι U.1.ι).hom.curve.w
  · change (pullSection g s).left ≫ c.hom ≫ e.hom = _
    rw [← Category.assoc]
    change ((pullSection (U.1.ι ≫ B.ι) s).left ≫
      (E.baseChangeCompIso B.ι U.1.ι).hom.curve.left) ≫ e.hom = _
    rw [baseChangeCompIso_section]
    exact hs

end FLT.Mazur.GeneralizedEllipticCurve
