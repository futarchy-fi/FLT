/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeIdealOpenExtension
public import FLT.Mazur.OpenIdealExtensionBaseChange

/-!
# Naturality of full relative ideal extension

The square relating original ambient inclusion and arbitrary parameter base
change is cartesian. Consequently extension of finite locally free families
into a separated ambient commutes with arbitrary scheme base change as an
equality of full ideals.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open FLT.Mazur.FCurve FLT.Mazur.OpenIdealCover

universe u

namespace FLT.Mazur.ClosedIdealCover

set_option backward.isDefEq.respectTransparency false

variable {A B S X Y : Scheme.{u}} (a : A ⟶ S) (b : B ⟶ S)
variable (i : A ⟶ B) (hi : i ≫ b = a) (s : X ⟶ S) (t : Y ⟶ S)
variable (g : Y ⟶ X) (hg : g ≫ s = t)

/-- Original ambient maps commute with arbitrary parameter base change. -/
@[reassoc]
theorem relativeIdealAmbientHom_baseChange :
    relativeIdealAmbientMap a s t g hg ≫ relativeIdealAmbientHom a b i hi s =
      relativeIdealAmbientHom a b i hi t ≫ relativeIdealAmbientMap b s t g hg := by
  apply pullback.hom_ext <;>
    simp only [Category.assoc, relativeIdealAmbientHom_fst, relativeIdealAmbientMap_fst,
      relativeIdealAmbientHom_fst_assoc, relativeIdealAmbientMap_snd,
      relativeIdealAmbientHom_snd, relativeIdealAmbientMap_snd_assoc]

/-- Base change of an original ambient morphism forms an actual cartesian square. -/
theorem relativeIdealAmbientHom_baseChange_isPullback :
    IsPullback (relativeIdealAmbientMap a s t g hg) (relativeIdealAmbientHom a b i hi t)
      (relativeIdealAmbientHom a b i hi s) (relativeIdealAmbientMap b s t g hg) := by
  have h : IsPullback (relativeIdealAmbientMap a s t g hg)
      (relativeIdealAmbientHom a b i hi t ≫ pullback.fst t b)
      (relativeIdealAmbientHom a b i hi s ≫ pullback.fst s b) g := by
    rw [relativeIdealAmbientHom_fst, relativeIdealAmbientHom_fst]
    exact relativeIdealAmbientMap_isPullback a s t g hg
  exact h.of_bot (relativeIdealAmbientHom_baseChange a b i hi s t g hg)
    (relativeIdealAmbientMap_isPullback b s t g hg)

variable [IsOpenImmersion i] [IsSeparated b] (d : ℕ)

/-- Extending a full family commutes with every arbitrary parameter base change. -/
theorem relativeIdealFamilyExtension_natural (J : RelativeIdealFamilies a d s) :
    relativeIdealFamilyBaseChange b d s t g hg
        (relativeIdealFamilyExtension a b i hi s d J) =
      relativeIdealFamilyExtension a b i hi t d
        (relativeIdealFamilyBaseChange a d s t g hg J) := by
  apply Subtype.ext
  change (J.val.map (relativeIdealAmbientHom a b i hi s)).comap
      (relativeIdealAmbientMap b s t g hg) =
    (J.val.comap (relativeIdealAmbientMap a s t g hg)).map (relativeIdealAmbientHom a b i hi t)
  have h : FiniteLocallyFreeDegree
      (J.val.subschemeι ≫ relativeIdealAmbientHom a b i hi s ≫ pullback.fst s b) d := by
    rw [relativeIdealAmbientHom_fst]
    exact J.property
  let _ := h.1
  let _ := finiteFamily_closed (relativeIdealAmbientHom a b i hi s) (pullback.fst s b) J.val
  exact openIdealExtension_baseChange _ _ _ _
    (relativeIdealAmbientHom_baseChange_isPullback a b i hi s t g hg) J.val

end FLT.Mazur.ClosedIdealCover
