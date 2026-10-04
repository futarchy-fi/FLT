/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineTrivialLineSectionOpen
public import FLT.Mazur.LineSectionTwistSystem
public import FLT.Mazur.CurveGenericLineComparison

/-!
# Nonzero sections and finite-support transition cokernels

On a reduced scheme an empty generator open forces a line section to vanish.
On an integral curve a nonzero section therefore generates at the generic
point, so every coherent twist transition has finite-support cokernel.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open Scheme.Modules

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FLT.Mazur.FCurve

variable {X : Scheme} {L : X.Modules}

/-- A line section with empty generator open is zero on a reduced scheme. -/
theorem section_eq_zero_of_generatorOpen_eq_bot [IsReduced X]
    (hL : LocallyFreeRankOne L) (s : Γ(L, ⊤))
    (hs : sectionGeneratorOpen L s = ⊥) : s = 0 := by
  apply TopCat.Presheaf.section_ext
    (⟨L.presheaf, L.isSheaf⟩ : TopCat.Sheaf Ab X)
  intro x hx
  obtain ⟨U, hxU, ⟨e⟩⟩ := hL x
  let t : Γ(L.restrict U.ι, ⊤) :=
    L.presheaf.map (homOfLE (show U.ι ''ᵁ ⊤ ≤ ⊤ from le_top)).op s
  have ht : U.toScheme.basicOpen (e.hom.app ⊤ t) = ⊥ := by
    rw [← sectionGeneratorOpen_structure, sectionGeneratorOpen_iso]
    change sectionGeneratorOpen (L.restrict U.ι)
      (L.presheaf.map (homOfLE (show U.ι ''ᵁ ⊤ ≤ ⊤ from le_top)).op s) = ⊥
    rw [sectionGeneratorOpen_restrict hL U.ι s, hs]
    rfl
  have hz : t = 0 := by
    apply (ConcreteCategory.bijective_of_isIso (e.hom.app ⊤)).injective
    exact (eq_zero_of_basicOpen_eq_bot _ ht).trans (map_zero _).symm
  let V := U.ι ''ᵁ ⊤
  have hxV : x ∈ V := by simpa [V] using hxU
  change L.presheaf.germ ⊤ x hx s = L.presheaf.germ ⊤ x hx 0
  rw [map_zero, ← L.presheaf.germ_res_apply (homOfLE (show V ≤ ⊤ from le_top)) x hxV s]
  change L.presheaf.germ V x hxV t = 0
  rw [hz, map_zero]

/-- Every nonzero line section generates on a nonempty open of a reduced scheme. -/
theorem sectionGeneratorOpen_nonempty [IsReduced X]
    (hL : LocallyFreeRankOne L) (s : Γ(L, ⊤)) (hs : s ≠ 0) :
    (sectionGeneratorOpen L s : Set X).Nonempty := by
  by_contra h
  exact hs (section_eq_zero_of_generatorOpen_eq_bot hL s
    (by simpa only [Opens.not_nonempty_iff_eq_bot] using h))

/-- A nonzero line section generates at the generic point of an integral scheme. -/
theorem genericPoint_mem_sectionGeneratorOpen [IsIntegral X]
    (hL : LocallyFreeRankOne L) (s : Γ(L, ⊤)) (hs : s ≠ 0) :
    genericPoint X ∈ sectionGeneratorOpen L s := by
  obtain ⟨x, hx⟩ := sectionGeneratorOpen_nonempty hL s hs
  exact ((genericPoint_spec X).mem_open_set_iff (sectionGeneratorOpen L s).isOpen).mpr
    ⟨x, trivial, hx⟩

namespace LineSectionTwistSystem

open ModuleSheafTensor ModuleLineBundleTensorPullback
open CoherentDevissage FLT.Mazur.GlobalIdealPower FLT.Mazur.GenericIdealInjection

/-- Every coherent twist transition has finite-support cokernel on an integral curve. -/
theorem step_cokernel_finiteSupport [IsNoetherian X] [IsIntegral X]
    (hd : topologicalKrullDim X ≤ 1) (M : X.Modules) [M.IsFinitePresentation]
    (hL : LocallyFreeRankOne L) (s : Γ(L, ⊤)) (hs : s ≠ 0) (n : ℕ) :
    (support (cokernel (step M s n))).Finite := by
  have := (hL.tensorPower n).isFinitePresentation
  have := (hL.tensorPower (n + 1)).isFinitePresentation
  have := tensor_coherent M (tensorPower L n)
  have := tensor_coherent M (tensorPower L (n + 1))
  have := step_isIso_on_generatorOpen M s n
  have := stalk_isIso_of_restrict (step M s n) (sectionGeneratorOpen L s)
    (genericPoint X) (genericPoint_mem_sectionGeneratorOpen hL s hs)
  exact finite_cokernel_support_of_generic_isIso hd (step M s n)

end LineSectionTwistSystem
end FLT.Mazur.FCurve
