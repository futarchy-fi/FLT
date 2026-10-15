/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.ModuleSectionRatioOpenNaturality
public import FLT.Mazur.ModuleSectionProjectiveChart

/-!
# Projective section charts commute with arbitrary pullback

Both coefficient and ratio maps are preserved on the original inverse-image
opens. This applies to closed infinitesimal restrictions as well as open charts.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite Scheme.Modules
namespace FLT.Mazur.FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local instance] MvPolynomial.gradedAlgebra
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules)
  {R : Type u} [CommRing R] (d : ℕ) (t : Fin (d + 1) → Γ(M, ⊤))
  (i : Fin (d + 1)) (U : Y.Opens) (V : X.Opens) (hV : V ≤ f ⁻¹ᵁ U)
  (hi : U ≤ sectionGeneratorOpen M (t i))
  (hiV : V ≤ sectionGeneratorOpen ((pullback f).obj M) (pullGlobal f M (t i)))
  (r : R →+* Γ(Y, U))

/-- The original chart algebra maps commute with the actual section pullback. -/
theorem sectionProjectiveChartRingMap_pullback :
    (f.appLE U V hV).hom.comp (sectionProjectiveChartRingMap M d t i U hi r) =
      sectionProjectiveChartRingMap ((pullback f).obj M) d
        (fun j ↦ pullGlobal f M (t j)) i V hiV ((f.appLE U V hV).hom.comp r) := by
  apply ProjectiveSpace.chartRing_hom_ext R (Fin (d + 1)) i
  · intro a
    simp only [RingHom.comp_apply, sectionProjectiveChartRingMap_scalar]
  · intro j
    simp only [RingHom.comp_apply, sectionProjectiveChartRingMap_coordinate]
    exact sectionRatioOn_pullback f M U V hV (t i) (t j) hi hiV

/-- Top-open transport of sections is compatible with the actual restricted morphism. -/
theorem resLE_topIso_inv (a : Γ(Y, U)) :
    (f.resLE U V hV).appTop (U.topIso.inv a) = V.topIso.inv (f.appLE U V hV a) := by
  simp only [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top, CommRingCat.comp_apply,
    ← CommRingCat.comp_apply U.topIso.inv U.topIso.hom, Iso.inv_hom_id,
    CommRingCat.id_apply]

/-- The actual projective-space chart morphisms retain the original coefficient map. -/
theorem sectionProjectiveChartMorphism_pullback :
    f.resLE U V hV ≫ sectionProjectiveChartMorphism M d t i U hi r =
      sectionProjectiveChartMorphism ((pullback f).obj M) d
        (fun j ↦ pullGlobal f M (t j)) i V hiV ((f.appLE U V hV).hom.comp r) := by
  rw [sectionProjectiveChartMorphism, ← Category.assoc, Scheme.toSpecΓ_naturality]
  simp only [sectionProjectiveChartMorphism, Category.assoc]
  rw [← Spec.map_comp_assoc]
  congr 2
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  change (f.resLE U V hV).appTop
    (U.topIso.inv (sectionProjectiveChartRingMap M d t i U hi r z)) = _
  rw [resLE_topIso_inv]
  exact congrArg V.topIso.inv
    (DFunLike.congr_fun (sectionProjectiveChartRingMap_pullback f M d t i U V hV hi hiV r) z)

end FLT.Mazur.FCurve
