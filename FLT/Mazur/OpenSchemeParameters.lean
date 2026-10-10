/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-!
# Parameters in an actual open subscheme

Morphisms over a base into an open subscheme are exactly the ambient
morphisms whose range lies in the open. The equivalence uses the actual
open-immersion lift and is compatible with precomposition.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace FLT.Mazur.OpenIdealCover

variable {H S X Y : Scheme.{u}} (p : H ⟶ S) (U : H.Opens) (s : X ⟶ S)

/-- Parameters of an actual open are exactly supported parameters of the ambient scheme. -/
def openSchemeParameterEquiv :
    { f : X ⟶ U.toScheme // f ≫ U.ι ≫ p = s } ≃
      { f : { f : X ⟶ H // f ≫ p = s } // Set.range f.val ⊆ U } where
  toFun f := ⟨⟨f.val ≫ U.ι, (Category.assoc _ _ _).trans f.property⟩, by
    rintro _ ⟨x, rfl⟩
    exact (f.val x).property⟩
  invFun f := ⟨IsOpenImmersion.lift U.ι f.val.val (by
    simpa only [Scheme.Opens.range_ι] using f.property), by
    rw [← Category.assoc, IsOpenImmersion.lift_fac]
    exact f.val.property⟩
  left_inv f := by
    apply Subtype.ext
    apply (cancel_mono U.ι).mp
    exact IsOpenImmersion.lift_fac _ _ _
  right_inv f := Subtype.ext (Subtype.ext (IsOpenImmersion.lift_fac _ _ _))

/-- Forgetting an open parameter is composition with its actual open immersion. -/
theorem openSchemeParameterEquiv_val
    (f : { f : X ⟶ U.toScheme // f ≫ U.ι ≫ p = s }) :
    (openSchemeParameterEquiv p U s f).val.val = f.val ≫ U.ι := rfl

/-- The constructed lift of an ambient parameter recovers its actual morphism. -/
theorem openSchemeParameterEquiv_symm_fac
    (f : { f : { f : X ⟶ H // f ≫ p = s } // Set.range f.val ⊆ U }) :
    ((openSchemeParameterEquiv p U s).symm f).val ≫ U.ι = f.val.val :=
  IsOpenImmersion.lift_fac _ _ _

/-- Precomposition commutes with forgetting an open parameter. -/
theorem openSchemeParameterEquiv_precomp (t : Y ⟶ S) (g : Y ⟶ X) (hg : g ≫ s = t)
    (f : { f : X ⟶ U.toScheme // f ≫ U.ι ≫ p = s }) :
    (openSchemeParameterEquiv p U t ⟨g ≫ f.val, by
      rw [Category.assoc, f.property, hg]⟩).val.val =
      g ≫ (openSchemeParameterEquiv p U s f).val.val := Category.assoc _ _ _

end FLT.Mazur.OpenIdealCover
