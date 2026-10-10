/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSectionCocycleEvaluation

/-!
# Local normalization after cocycle pullback

Composing the cocycle pullback comparison with descent by actual generators
sends the pulled-back basis to its prescribed original section morphism.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Scheme.Modules

namespace FLT.Mazur.FCurve

open ModuleSheafUnitCocycle

universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {X Y : Scheme.{u}} {ι : Type u} (U : ι → Y.Opens)
  (g : Cocycle U) (hU : iSup U = ⊤) (p : X ⟶ Y) (M : X.Modules)
  (t : ι → Γ(M, ⊤)) (ht : ∀ i, p ⁻¹ᵁ U i ≤ sectionGeneratorOpen M (t i))
  (hg : ∀ i j V hi hj, ((g.inverseImage p).unit i j V hi hj : Γ(X, V)) =
    sectionRatioOn M (t i) V (hi.trans (ht i)) (t j))

/-- The composed global comparison has the prescribed local generator normalization. -/
theorem sectionCocyclePullback_normalization (i : ι) :
    (restrictFunctor (p ⁻¹ᵁ U i).ι).map
        ((g.pullbackIso p hU).hom ≫
          (sectionCocycleIso M (fun i ↦ p ⁻¹ᵁ U i) t ht (g.inverseImage p)
            (Cocycle.inverseImage_cover p hU) hg).hom) =
      (modulePullbackTrivialization p (g.restrictIso i)).hom ≫
        sectionHom M (p ⁻¹ᵁ U i) (M.presheaf.map (homOfLE le_top).op (t i)) := by
  rw [Functor.map_comp, ← Functor.mapIso_hom, g.pullbackIso_restrict,
    sectionCocycleIso_restrict M (fun i ↦ p ⁻¹ᵁ U i) t ht (g.inverseImage p)
      (Cocycle.inverseImage_cover p hU) hg i]
  simp only [Cocycle.localPullbackComparison, sectionCocycleLocalIso,
    Iso.trans_hom, Iso.symm_hom, asIso_hom, Category.assoc, Iso.inv_hom_id_assoc]

end FLT.Mazur.FCurve
