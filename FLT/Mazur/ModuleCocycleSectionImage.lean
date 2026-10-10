/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleCocycleChartSections
public import FLT.Mazur.ModuleLocalSectionEvaluation
public import FLT.Mazur.ModuleUnitCocyclePullback

/-!
# Images of pulled cocycle sections

Local normalization and the original chart coefficients determine the global image.
All chart-isomorphism calculations take place before geometric specialization.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Scheme.Modules

namespace FLT.Mazur.FCurve

open ModuleSheafUnitCocycle

universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {X Y : Scheme.{u}} {ι : Type u} {U : ι → Y.Opens} (g : Cocycle U)
  (p : X ⟶ Y) (M : X.Modules) (t : ι → Γ(M, ⊤))
  (a : (pullback p).obj g.sheaf ⟶ M)
  (ha : ∀ i, (restrictFunctor (p ⁻¹ᵁ U i).ι).map a =
    (modulePullbackTrivialization p (g.restrictIso i)).hom ≫
      sectionHom M (p ⁻¹ᵁ U i) (M.presheaf.map (homOfLE le_top).op (t i)))

include ha

/-- The original pulled chart coefficient computes the local image of a global section. -/
theorem cocycleSection_image_local (s : Γ(g.sheaf, ⊤)) (i : ι) :
    M.presheaf.map (homOfLE (show (p ⁻¹ᵁ U i).ι ''ᵁ ⊤ ≤ ⊤ from le_top)).op
        (a.app ⊤ (pullGlobal p g.sheaf s)) =
      (show Γ(X, (p ⁻¹ᵁ U i).ι ''ᵁ ⊤) from
        (p ∣_ U i).appTop (g.chartValue i s)) •
          M.presheaf.map (homOfLE le_top).op (t i) := by
  rw [hom_globalSection_restrict (p ⁻¹ᵁ U i) a _ (t i) (ha i),
    g.pullGlobal_chartValue]

/-- Matching the original chart coefficients identifies the global section image. -/
theorem cocycleSection_image (hU : iSup U = ⊤) (s : Γ(g.sheaf, ⊤)) (v : Γ(M, ⊤))
    (hv : ∀ i, (show Γ(X, (p ⁻¹ᵁ U i).ι ''ᵁ ⊤) from
        (p ∣_ U i).appTop (g.chartValue i s)) •
          M.presheaf.map
            (homOfLE (show (p ⁻¹ᵁ U i).ι ''ᵁ ⊤ ≤ ⊤ from le_top)).op (t i) =
      M.presheaf.map (homOfLE le_top).op v) :
    a.app ⊤ (pullGlobal p g.sheaf s) = v := by
  refine TopCat.Sheaf.eq_of_locally_eq'
    (⟨M.presheaf, M.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat X)
    (fun i ↦ (p ⁻¹ᵁ U i).ι ''ᵁ ⊤) ⊤ (fun _ ↦ homOfLE le_top) ?_ _ _ ?_
  · simpa only [Scheme.Opens.ι_image_top] using
      le_of_eq (Cocycle.inverseImage_cover p hU).symm
  · intro i
    exact (cocycleSection_image_local g p M t a ha s i).trans (hv i)

end FLT.Mazur.FCurve
