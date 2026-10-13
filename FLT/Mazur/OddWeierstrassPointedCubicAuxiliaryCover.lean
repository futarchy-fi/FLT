/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurvePointedCubicFamily
public import FLT.Mazur.OddWeierstrassOriginalAuxiliaryCover

/-!
# Odd-chart full auxiliary labels over the original pointed cubic base

The original coefficient cover is pulled back along the actual canonical spectrum
map. Its complete labeling belongs to the established pointed cubic family, and
the resulting cover is etale and surjective over the original base scheme.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open scoped CategoryTheory.Obj
namespace FLT.Mazur.OddWeierstrassParameter
open WeierstrassIntegralChart GeneralizedEllipticCurve AuxiliaryLevel
open UniversalWeierstrass (Labels)
open IntegralWeierstrassParameter (oddChartEquation oddChart_discriminant)
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} (W : WeierstrassCurve Γ(S, ⊤)) [W.IsElliptic]
  (h₃ : IsUnit (3 : Γ(S, ⊤)))
local notation "hΔ" => WeierstrassCurve.IsElliptic.isUnit (W := W)
local notation "G" => integralCurveGroup W hΔ

/-- The actual auxiliary cover on the original base, with its coefficients unchanged. -/
def pointedCubicAuxiliaryCover : Over S :=
  (Over.pullback S.toSpecΓ).obj (originalAuxiliaryCover W h₃ hΔ)

/-- The pulled coefficient cover is etale over the original base. -/
instance pointedCubicAuxiliaryCover_etale : Etale (pointedCubicAuxiliaryCover W h₃).hom :=
  inferInstanceAs (Etale (pullback.snd (originalAuxiliaryCover W h₃ hΔ).hom S.toSpecΓ))

/-- Every original base point has an auxiliary labeling after this actual cover. -/
instance pointedCubicAuxiliaryCover_surjective :
    Surjective (pointedCubicAuxiliaryCover W h₃).hom :=
  inferInstanceAs (Surjective (pullback.snd (originalAuxiliaryCover W h₃ hΔ).hom S.toSpecΓ))

/-- The original coefficient-cover projection as a relative morphism. -/
def pointedCubicAuxiliaryProjection :
    (Over.map S.toSpecΓ).obj (pointedCubicAuxiliaryCover W h₃) ⟶
      originalAuxiliaryCover W h₃ hΔ :=
  Over.homMk (pullback.fst (originalAuxiliaryCover W h₃ hΔ).hom S.toSpecΓ)
    pullback.condition

/-- The original pulled cubic carrier is separated. -/
local instance : IsSeparated (pointedCubicFamily W).group.hom :=
  inferInstanceAs (IsSeparated (pullback.snd (integralCurveStructure W) S.toSpecΓ))

/-- The bundled coefficient pullback has the same separated carrier. -/
local instance : IsSeparated ((Over.pullback S.toSpecΓ).mapCommGrp.obj G).X.hom :=
  inferInstanceAs (IsSeparated (pullback.snd (integralCurveStructure W) S.toSpecΓ))

/-- Full auxiliary labels on the actual pointed cubic family. -/
def pointedCubicAuxiliaryParameter : pointedCubicAuxiliaryCover W h₃ ⟶
    faithfulScheme (pointedCubicFamily W).group (Labels 3) :=
  cartesianGroupParameter S.toSpecΓ G ((Over.pullback S.toSpecΓ).mapCommGrp.obj G)
    (Iso.refl _) (Labels 3)
    (pointedCubicAuxiliaryProjection W h₃ ≫ originalAuxiliaryParameter W h₃ hΔ)

/-- The labels retain the original coefficient-cover marking after projection. -/
theorem pointedCubicAuxiliaryParameter_value (a : Labels 3) :
    (pointedCubicAuxiliaryParameter W h₃ ≫ faithfulInclusion _ (Labels 3) ≫
      value _ (Labels 3) a).left ≫ pullback.fst (G).X.hom S.toSpecΓ =
        (pointedCubicAuxiliaryProjection W h₃ ≫ originalAuxiliaryParameter W h₃ hΔ ≫
          faithfulInclusion (G).X (Labels 3) ≫ value (G).X (Labels 3) a).left := by
  change (cartesianGroupParameter S.toSpecΓ G
    ((Over.pullback S.toSpecΓ).mapCommGrp.obj G) (Iso.refl _) (Labels 3)
    (pointedCubicAuxiliaryProjection W h₃ ≫ originalAuxiliaryParameter W h₃ hΔ) ≫
      faithfulInclusion ((Over.pullback S.toSpecΓ).mapCommGrp.obj G).X (Labels 3) ≫
      value ((Over.pullback S.toSpecΓ).mapCommGrp.obj G).X (Labels 3) a).left ≫ _ = _
  rw [cartesianGroupParameter_value]
  have h := cartesianGroupMarking_projection S.toSpecΓ G
    ((Over.pullback S.toSpecΓ).mapCommGrp.obj G)
      (Iso.refl _) (Labels 3)
      (pointedCubicAuxiliaryProjection W h₃ ≫ originalAuxiliaryParameter W h₃ hΔ) a
  change (cartesianGroupMarking S.toSpecΓ G
    ((Over.pullback S.toSpecΓ).mapCommGrp.obj G) (Iso.refl _) (Labels 3)
    (pointedCubicAuxiliaryProjection W h₃ ≫ originalAuxiliaryParameter W h₃ hΔ) a).left ≫
      (𝟙 _) ≫ pullback.fst (G).X.hom S.toSpecΓ = _ at h
  simpa only [Category.id_comp, Category.assoc] using h

end FLT.Mazur.OddWeierstrassParameter
