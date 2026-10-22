/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSectionRegularity

/-!
# Global sections through a commuting pullback square

The comparison around the square identifies restriction of a transported
section with transport of its restriction. This is proved before specializing
to divisor powers, keeping large sheaf implementations out of conversion.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Scheme.Modules.pullback
variable {P X T S : Scheme} (p : P ⟶ X) (t : T ⟶ P) (g : T ⟶ S) (s : S ⟶ X)
  (w : t ≫ p = g ≫ s) {M : X.Modules} {N : P.Modules}
  (e : (pullback p).obj M ≅ N)

/-- The induced comparison between restrictions along the two sides of the square. -/
def sectionSquareTransportIso :
    (pullback g).obj ((pullback s).obj M) ≅ (pullback t).obj N :=
  (pullbackComp g s).app M ≪≫ (pullbackCongr w.symm).app M ≪≫
    ((pullbackComp t p).app M).symm ≪≫ (pullback t).mapIso e

/-- The square comparison preserves the original section, including its actual value. -/
theorem sectionSquareTransportIso_sections (x : Γ(M, ⊤)) :
    (sectionSquareTransportIso p t g s w e).hom.app ⊤
      (pullGlobal g _ (pullGlobal s _ x)) =
        pullGlobal t _ (e.hom.app ⊤ (pullGlobal p _ x)) := by
  simp only [sectionSquareTransportIso, Iso.trans_hom, Iso.app_hom,
    Iso.symm_hom, Iso.app_inv, Functor.mapIso_hom, Hom.comp_app,
    ConcreteCategory.comp_apply]
  change ((pullback t).map e.hom).app ⊤
    (((pullbackComp t p).inv.app M).app ⊤
      (((pullbackCongr w.symm).hom.app M).app ⊤
        (((pullbackComp g s).hom.app M).app ⊤
          (pullGlobal g _ (pullGlobal s M x))))) = _
  rw [pullGlobal_comp_hom g s M, pullGlobal_congr w.symm,
    pullGlobal_comp t p M, pullGlobal_naturality]

end FLT.Mazur.FCurve
