/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CoherentDevissage
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits

/-!
# Exactness of module stalks

Forgetting the module action commutes with sheafification and preserves finite
colimits. Consequently module short exact sequences are exact on additive stalks.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace FLT.Mazur.FCurve.CoherentDevissage

variable (X : Scheme.{u})

/-- Forgetting a module action preserves finite colimits of sheaves. -/
instance moduleToSheaf_preservesFiniteColimits :
    PreservesFiniteColimits (SheafOfModules.toSheaf.{u} X.ringCatSheaf) where
  preservesFiniteColimits J _ _ := by
    let R := X.ringCatSheaf
    let L := PresheafOfModules.sheafification.{u} (𝟙 R.obj)
    let U := SheafOfModules.toSheaf.{u} R
    have : PreservesColimitsOfShape J (L ⋙ U) :=
      inferInstanceAs (PreservesColimitsOfShape J
        (PresheafOfModules.toPresheaf.{u} R.obj ⋙ presheafToSheaf _ AddCommGrpCat.{u}))
    constructor
    intro K
    let D := K ⋙ (SheafOfModules.forget.{u} R ⋙
      PresheafOfModules.restrictScalars (𝟙 R.obj))
    have : PreservesColimit (D ⋙ L) U :=
      preservesColimit_of_preserves_colimit_cocone
        (isColimitOfPreserves L (colimit.isColimit D))
        (isColimitOfPreserves (L ⋙ U) (colimit.isColimit D))
    let e : D ⋙ L ≅ K := Functor.isoWhiskerLeft K
      (asIso (PresheafOfModules.sheafificationAdjunction.{u} (𝟙 R.obj)).counit)
    exact preservesColimit_of_iso_diagram U e

/-- The additive sheaf underlying a scheme module. -/
abbrev moduleToSheaf : X.Modules ⥤ TopCat.Sheaf AddCommGrpCat.{u} X :=
  SheafOfModules.toSheaf X.ringCatSheaf

instance moduleToSheaf_additive : (moduleToSheaf X).Additive where
  map_add := rfl

instance moduleToSheaf_finiteLimits : PreservesFiniteLimits (moduleToSheaf X) :=
  inferInstanceAs (PreservesFiniteLimits (SheafOfModules.toSheaf.{u} X.ringCatSheaf))

instance moduleToSheaf_finiteColimits : PreservesFiniteColimits (moduleToSheaf X) :=
  inferInstanceAs (PreservesFiniteColimits (SheafOfModules.toSheaf.{u} X.ringCatSheaf))

variable {X}

/-- Epimorphisms of module sheaves remain epimorphisms of additive sheaves. -/
theorem moduleToSheaf_map_epi {M N : X.Modules} (f : M ⟶ N) [Epi f] :
    Epi ((moduleToSheaf X).map f) := inferInstance

/-- Forgetting the module action preserves exact complexes. -/
theorem moduleToSheaf_exact {S : ShortComplex X.Modules} (hS : S.Exact) :
    (S.map (moduleToSheaf X)).Exact := hS.map _

/-- Module stalks preserve exact complexes. -/
theorem stalk_exact {S : ShortComplex X.Modules} (hS : S.Exact) (x : X) :
    (S.map (stalk x)).Exact :=
  (moduleToSheaf_exact hS).map
    (TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x)

/-- Forgetting the module action preserves short exact sequences. -/
theorem moduleToSheaf_shortExact {S : ShortComplex X.Modules} (hS : S.ShortExact) :
    (S.map (moduleToSheaf X)).ShortExact :=
  hS.map_of_exact _

/-- Module stalks preserve short exact sequences. -/
theorem stalk_shortExact {S : ShortComplex X.Modules} (hS : S.ShortExact) (x : X) :
    (S.map (stalk x)).ShortExact := by
  exact (moduleToSheaf_shortExact hS).map_of_exact
    (TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x)

/-- The support of the middle term is the union of the outer supports. -/
theorem support_shortExact {S : ShortComplex X.Modules} (hS : S.ShortExact) :
    support S.X₂ = support S.X₁ ∪ support S.X₃ := by
  ext x
  have h := stalk_shortExact hS x
  have := h.mono_f
  have := h.epi_g
  change (¬ IsZero ((stalk x).obj S.X₂)) ↔
    (¬ IsZero ((stalk x).obj S.X₁)) ∨ (¬ IsZero ((stalk x).obj S.X₃))
  rw [← not_and_or]
  apply not_congr
  constructor
  · intro hz
    exact ⟨hz.of_mono (S.map (stalk x)).f, hz.of_epi (S.map (stalk x)).g⟩
  · rintro ⟨h₁, h₃⟩
    exact h.exact.isZero_X₂ (h₁.eq_of_src _ _) (h₃.eq_of_tgt _ _)

end FLT.Mazur.FCurve.CoherentDevissage
