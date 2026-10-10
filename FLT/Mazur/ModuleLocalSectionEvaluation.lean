/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSheafMorphismGluing
public import FLT.Mazur.DivisorInvertibleSheaf

/-!
# Computing a module map from a local section normalization

A local expression as a coefficient map followed by a generating section
computes the restriction of every global image section.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Scheme.Modules

namespace FLT.Mazur.FCurve

universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {X : Scheme.{u}} {M N : X.Modules}

/-- A section-normalized local map computes the local coefficient of every global image. -/
theorem hom_globalSection_restrict (U : X.Opens) (a : M ⟶ N)
    (e : M.restrict U.ι ⟶ structureModule U.toScheme)
    (t : Γ(N, ⊤))
    (ha : (restrictFunctor U.ι).map a =
      e ≫ sectionHom N U (N.presheaf.map (homOfLE le_top).op t))
    (s : Γ(M, ⊤)) :
    N.presheaf.map (homOfLE (show U.ι ''ᵁ ⊤ ≤ ⊤ from le_top)).op (a.app ⊤ s) =
      (show Γ(X, U.ι ''ᵁ ⊤) from
        e.app ⊤ (M.presheaf.map (homOfLE le_top).op s)) •
          N.presheaf.map (homOfLE le_top).op t := by
  have hn := ConcreteCategory.congr_hom
    (a.mapPresheaf.naturality (homOfLE (show U.ι ''ᵁ ⊤ ≤ ⊤ from le_top)).op) s
  have hl := congrArg (fun b ↦ b.app ⊤ (M.presheaf.map (homOfLE le_top).op s)) ha
  change a.app (U.ι ''ᵁ ⊤) (M.presheaf.map (homOfLE le_top).op s) =
    (sectionHom N U (N.presheaf.map (homOfLE le_top).op t)).app ⊤
      (e.app ⊤ (M.presheaf.map (homOfLE le_top).op s)) at hl
  rw [sectionHom_app] at hl
  erw [N.smul_restrictAppIso_hom_apply U.ι ⊤] at hl
  rw [Scheme.Opens.ι_appIso] at hl
  simp only [Iso.refl_inv, ← Functor.map_comp_apply] at hl
  exact hn.symm.trans hl

end FLT.Mazur.FCurve
