/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CartierBoundarySectionRingNaturality

/-!
# Identity and degree laws for canonical Cartier section pullback

The canonical dual-ideal comparison at the identity induces the identity ring
map. Every canonical Cartier pullback preserves each tensor-degree component.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.FCurve
open SectionGradedSum SectionGradedMultiplication
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {X Y : Scheme}

/-- The canonical Cartier section map at an identity fixes every section. -/
theorem cartierSectionRingMap_id (I : X.IdealSheafData) (hI : EffectiveCartier I)
    (he : I.comap (𝟙 X) = I) :
    cartierSectionRingMap (𝟙 X) hI hI he = RingHom.id _ := by
  let _ : IsIso (idealModulePullbackHom I (𝟙 X)) :=
    idealModulePullbackHom_isIso_of_cartier _ hI (he.symm ▸ hI)
  change SectionGradedLinePullback.ringHom _ (divisorLinePullbackIsoOfEq _ hI hI he) = _
  rw [divisorLinePullbackIsoOfEq_id_eq (𝟙 X) rfl I hI he]
  exact SectionGradedLinePullback.ringHom_id_eq _ rfl _

/-- Canonical Cartier pullback retains the specified homogeneous tensor degree. -/
theorem cartierSectionRingMap_mem_grade (f : X ⟶ Y)
    {I : Y.IdealSheafData} {J : X.IdealSheafData}
    (hI : EffectiveCartier I) (hJ : EffectiveCartier J) (hf : I.comap f = J)
    (d : ℕ) {s : SectionGradedSum.Sections (divisorLineBundle I hI) ⊤}
    (hs : s ∈ grade (divisorLineBundle I hI) ⊤ d) :
    cartierSectionRingMap f hI hJ hf s ∈ grade (divisorLineBundle J hJ) ⊤ d := by
  let _ : IsIso (idealModulePullbackHom I f) :=
    idealModulePullbackHom_isIso_of_cartier f hI (hf.symm ▸ hJ)
  obtain ⟨s, rfl⟩ := hs
  exact ⟨_, (SectionGradedLinePullback.ringHom_of f
    (divisorLinePullbackIsoOfEq f hI hJ hf) d s).symm⟩

end FLT.Mazur.FCurve
