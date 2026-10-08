/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineRelativeFiberCriterion
public import FLT.Mazur.ModuleSectionProjectiveOver
public import FLT.Mazur.ProjectiveSpaceProper

/-!
# Finiteness of a section morphism near an affine section-covered fiber

A globally generating family whose generator opens are affine on one
fiber gives a projective-space morphism that is finite near that base
point. All chart equalities use the actual section morphism.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

namespace FLT.Mazur.FCurve

open ProjectiveSpace

variable {X : Scheme.{0}} {R : Type} [CommRing R]
  (q : X ⟶ Spec (.of R)) [IsProper q] (M : X.Modules)
  (n : ℕ) (t : Fin (n + 1) → Γ(M, ⊤))
  (ht : ⨆ i, sectionGeneratorOpen M (t i) = ⊤) (s : Spec (.of R))

/-- Affine generator opens on one fiber make the actual section morphism finite nearby. -/
theorem sectionProjectiveMorphism_finite_neighborhood
    (haff : ∀ i, IsAffineOpen (q.fiberι s ⁻¹ᵁ sectionGeneratorOpen M (t i))) :
    ∃ V : (Spec (.of R)).Opens, s ∈ V ∧
      IsFinite ((sectionProjectiveMorphism M n t ht
        (q.appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)) ∣_
          (baseProjection R (Fin (n + 1)) ⁻¹ᵁ V)) := by
  let g := sectionProjectiveMorphism M n t ht
    (q.appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)
  have hg : g ≫ baseProjection R (Fin (n + 1)) = q :=
    sectionProjectiveMorphism_baseProjection M n t ht q
  let _ : IsProper (g ≫ baseProjection R (Fin (n + 1))) := hg.symm ▸ inferInstance
  apply RelativeFiber.exists_finite_neighborhood_of_affine_charts g
    (baseProjection R (Fin (n + 1))) s (chart R (Fin (n + 1)))
    (fun i ↦ .of_isIso (chartIso R (Fin (n + 1)) i).hom) (iSup_chart R _)
  intro i
  rw [hg, sectionProjectiveMorphism_preimage_chart]
  exact haff i

end FLT.Mazur.FCurve
