/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicRelativeRecoverySections
public import FLT.Mazur.IdealAdicRelativeRecoveryRefinement
public import FLT.Mazur.ModuleSheafOpenImmersionRefinementSections

/-!
# Affine recovery on restricted image sections

The actual affine recovery maps intertwine section restriction with the
original coefficient sheaf maps, evaluated on genuine pullback unit sections.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

universe u

namespace FLT.Mazur.IdealAdicGradedPullback

open ModuleSheafOpenImmersionSections SheafPullbackPathComparison

/-- Pullback units commute with global sections of arbitrary module morphisms. -/
lemma pullbackUnit_top_naturality {A B : Scheme.{u}} (p : A ⟶ B)
    {M N : B.Modules} (a : M ⟶ N) :
    a.app ⊤ ≫ ((pullbackPushforwardAdjunction p).unit.app N).app ⊤ =
      ((pullbackPushforwardAdjunction p).unit.app M).app ⊤ ≫ ((pullback p).map a).app ⊤ := by
  exact congrArg (fun k ↦ k.app ⊤) ((pullbackPushforwardAdjunction p).unit.naturality a)

/-- A geometric recovery square induces the corresponding square of range sections. -/
lemma recovery_topSections_refine {A B C : Scheme.{u}} (p : C ⟶ B) (i : B ⟶ A)
    (r : C ⟶ A) [IsOpenImmersion i] [IsOpenImmersion r] (e : p ≫ i = r)
    (M : A.Modules) (N : B.Modules) (P : C.Modules)
    (a : (pullback i).obj M ⟶ N) (b : (pullback r).obj M ⟶ P)
    (c : (pullback p).obj N ⟶ P)
    (h : (pullback p).map a ≫ c = (comparison p i r e).hom.app M ≫ b) :
    M.presheaf.map (homOfLE (refinement_opensRange_le p i r e)).op ≫
        (topSectionsIso r M).hom ≫ b.app ⊤ =
      (topSectionsIso i M).hom ≫ a.app ⊤ ≫
        ((pullbackPushforwardAdjunction p).unit.app N).app ⊤ ≫ c.app ⊤ := by
  rw [← Category.assoc, topSectionsIso_refine p i r e M]
  have hs := congrArg (fun k ↦ k.app ⊤) h
  simp only [Hom.comp_app] at hs
  simp only [Category.assoc]
  rw [← hs, ← Category.assoc _ _ (c.app ⊤), ← pullbackUnit_top_naturality, Category.assoc]

variable {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsAffine Y]
variable (J : Y.IdealSheafData) (f : X ⟶ Y)

attribute [local instance] relativeTensorChart_isOpenImmersion
attribute [local irreducible] Scheme.Modules.pullback relativeChartCoefficientSheaf
attribute [local irreducible] relativeDescendedCoefficientSheaf relativeCoefficientSheafMap

/-- The canonical chart section maps preserve further original affine restrictions. -/
lemma relativeDescendedImagePullbackSectionsIso_refine {U V : X.affineOpens}
    (i : U.1 ⟶ V.1) :
    (relativeDescendedCoefficientSheaf J f).presheaf.map
        (homOfLE (relativeTensorImageOpen_mono J f i)).op ≫
          (relativeDescendedImagePullbackSectionsIso J f U).hom =
      (relativeDescendedImagePullbackSectionsIso J f V).hom ≫
        ((pullbackPushforwardAdjunction (relativeTensorTransition J f i)).unit.app
          ((pullback (relativeTensorChart J f V)).obj
            (relativeDescendedCoefficientSheaf J f))).app ⊤ ≫
          ((comparison (relativeTensorTransition J f i) (relativeTensorChart J f V)
            (relativeTensorChart J f U) (relativeTensorTransition_chart J f i)).hom.app
              (relativeDescendedCoefficientSheaf J f)).app ⊤ :=
  topSectionsIso_refine (relativeTensorTransition J f i) (relativeTensorChart J f V)
    (relativeTensorChart J f U) (relativeTensorTransition_chart J f i)
    (relativeDescendedCoefficientSheaf J f)

attribute [local irreducible] relativeDescendedAffineRecoveryIso
attribute [local irreducible] relativeTensorTransition relativeTensorChart

/-- Restricted affine recovery is coefficient transition applied to the chart unit. -/
lemma relativeDescendedAffineRecoveryIso_sections_refine {U V : X.affineOpens}
    (i : U.1 ⟶ V.1) :
    (relativeDescendedCoefficientSheaf J f).presheaf.map
        (homOfLE (relativeTensorImageOpen_mono J f i)).op ≫
          (relativeDescendedImagePullbackSectionsIso J f U).hom ≫
            (relativeDescendedAffineRecoveryIso J f (𝟙 U.1)).hom.app ⊤ =
      (relativeDescendedImagePullbackSectionsIso J f V).hom ≫
        (relativeDescendedAffineRecoveryIso J f (𝟙 V.1)).hom.app ⊤ ≫
          ((pullbackPushforwardAdjunction (relativeTensorTransition J f i)).unit.app
            (relativeChartCoefficientSheaf J f V)).app ⊤ ≫
              (relativeCoefficientSheafMap J f i).app ⊤ := by
  have hr := relativeDescendedAffineRecoveryIso_refine J f (𝟙 V.1) i
  rw [relativeDescendedAffineRecoveryIso_eq_self J f (i ≫ 𝟙 V.1)] at hr
  exact recovery_topSections_refine (relativeTensorTransition J f i)
    (relativeTensorChart J f V) (relativeTensorChart J f U)
    (relativeTensorTransition_chart J f i) (relativeDescendedCoefficientSheaf J f)
    (relativeChartCoefficientSheaf J f V) (relativeChartCoefficientSheaf J f U)
    (relativeDescendedAffineRecoveryIso J f (𝟙 V.1)).hom
    (relativeDescendedAffineRecoveryIso J f (𝟙 U.1)).hom
    (relativeCoefficientSheafMap J f i) hr

end FLT.Mazur.IdealAdicGradedPullback
