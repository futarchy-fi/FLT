/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSectionCocycleIso

/-!
# Evaluation of the descended section comparison

The glued comparison retains its prescribed generator on each original
chart. These formulas also characterize its global module morphism.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Scheme.Modules

namespace FLT.Mazur.FCurve

open ModuleSheafUnitCocycle ModuleSheafMorphismGluing

universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {X : Scheme.{u}} (M : X.Modules) {ι : Type u} (U : ι → X.Opens)
  (t : ι → Γ(M, ⊤)) (ht : ∀ i, U i ≤ sectionGeneratorOpen M (t i))
  (g : Cocycle U) (hU : iSup U = ⊤)
  (hg : ∀ i j V hi hj, (g.unit i j V hi hj : Γ(X, V)) =
    sectionRatioOn M (t i) V (hi.trans (ht i)) (t j))

/-- The descended comparison restricts to the actual section map on each chart. -/
theorem sectionCocycleIso_restrict (i : ι) :
    (restrictFunctor (U i).ι).map (sectionCocycleIso M U t ht g hU hg).hom =
      (sectionCocycleLocalIso M U t ht g i).hom :=
  (existsUnique_glue_restrict U hU
    (fun j ↦ (sectionCocycleLocalIso M U t ht g j).hom)
    (sectionCocycleLocalIso_compatible M U t ht g hg)).choose_spec.1 i

/-- Evaluation on any generator subopen uses its actual section coefficient. -/
theorem sectionCocycleIso_app (i : ι) (V : X.Opens) (hi : V ≤ U i)
    (s : g.sections V) :
    (sectionCocycleIso M U t ht g hU hg).hom.app V s =
      g.evaluate i hi s • M.presheaf.map (homOfLE le_top).op (t i) := by
  have he : (sectionCocycleIso M U t ht g hU hg).hom.over (U i) =
      (restrictionEquiv (U i)).symm (sectionCocycleLocalIso M U t ht g i).hom := by
    apply (restrictionEquiv (U i)).injective
    rw [restrictionEquiv_over, sectionCocycleIso_restrict, Equiv.apply_symm_apply]
  exact (congrArg (fun a : g.sheaf.over (U i) ⟶ M.over (U i) ↦ localApp a hi s) he).trans
    (sectionCocycleLocalIso_localApp M U t ht g i V hi s)

/-- Its prescribed generator-chart restrictions determine the comparison uniquely. -/
theorem sectionCocycleIso_hom_unique (a : g.sheaf ⟶ M)
    (ha : ∀ i, (restrictFunctor (U i).ι).map a =
      (sectionCocycleLocalIso M U t ht g i).hom) :
    a = (sectionCocycleIso M U t ht g hU hg).hom := by
  apply hom_ext_restrict U hU
  intro i
  rw [ha, sectionCocycleIso_restrict]

end FLT.Mazur.FCurve
