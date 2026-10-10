/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealTwistTransitionExact
public import FLT.Mazur.FiniteSupportEulerPositive

/-!
# The actual exact sequence of a nonzero line section

On an integral curve a nonzero section embeds the structure sheaf in the
line bundle. Its cokernel has finite support, and the line's degree is the
actual dimension of that cokernel's sections. A degree-zero nonzero section
is everywhere generating; negative-degree lines have no nonzero sections.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open Scheme.Modules

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace FLT.Mazur.FCurve

open CoherentDevissage FLT.Mazur.GenericIdealInjection

variable {k : Type} [Field k] {X : Scheme} [IsIntegral X]
  (f : X ⟶ Spec (.of k)) [IsProper f]

/-- The actual homomorphism of a nonzero line section is injective. -/
theorem nonzero_globalSectionHom_mono {L : X.Modules}
    (hL : LocallyFreeRankOne L) (s : Γ(L, ⊤)) (hs : s ≠ 0) :
    Mono (globalSectionHom L s) := by
  let a := globalSectionHom L s
  have : IsIso ((restrictFunctor (sectionGeneratorOpen L s).ι).map a) :=
    inferInstanceAs (IsIso ((restrictFunctor (moduleHomIsoOpen a).ι).map a))
  have := stalk_isIso_of_restrict a (sectionGeneratorOpen L s) (genericPoint X)
    (genericPoint_mem_sectionGeneratorOpen hL s hs)
  exact mono_of_generic_mono_of_line_embedding structureModule_locallyFreeRankOne (𝟙 _) a

include f in
/-- The cokernel of a nonzero section has finite support on an integral curve. -/
theorem nonzero_globalSectionHom_cokernel_finiteSupport (hd : topologicalKrullDim X ≤ 1)
    {L : X.Modules} (hL : LocallyFreeRankOne L) (s : Γ(L, ⊤)) (hs : s ≠ 0) :
    (support (cokernel (globalSectionHom L s))).Finite := by
  have := Chow.source_isNoetherian f
  have := hL.isFinitePresentation
  have := (structureModule_locallyFreeRankOne (X := X)).isFinitePresentation
  let a := globalSectionHom L s
  have : IsIso ((restrictFunctor (sectionGeneratorOpen L s).ι).map a) :=
    inferInstanceAs (IsIso ((restrictFunctor (moduleHomIsoOpen a).ι).map a))
  have := stalk_isIso_of_restrict a (sectionGeneratorOpen L s) (genericPoint X)
    (genericPoint_mem_sectionGeneratorOpen hL s hs)
  exact finite_cokernel_support_of_generic_isIso hd a

/-- Degree is the actual cokernel's section dimension for any nonzero line section. -/
theorem line_degree_eq_section_cokernel_h0 (hd : topologicalKrullDim X ≤ 1)
    {L : X.Modules} (hL : LocallyFreeRankOne L) (s : Γ(L, ⊤)) (hs : s ≠ 0) :
    curveSheafDegree f L =
      (Module.finrank k (ModuleScalarH f (cokernel (globalSectionHom L s)) 0) : ℤ) := by
  have := Chow.source_isNoetherian f
  have := hL.isFinitePresentation
  have := (structureModule_locallyFreeRankOne (X := X)).isFinitePresentation
  let a := globalSectionHom L s
  have := nonzero_globalSectionHom_mono hL s hs
  have := coherent_cokernel a
  have hfin := nonzero_globalSectionHom_cokernel_finiteSupport f hd hL s hs
  have := finiteSupport_cohomology_subsingleton f (cokernel a) hfin 1 (by decide)
  have hadd := curveEulerCharacteristic_add_finiteSupport f
    (ShortComplex.cokernelSequence a) (coherent_cokernelSequence a) hfin
  change curveEulerCharacteristic f L =
    curveEulerCharacteristic f (structureModule X) + curveEulerCharacteristic f (cokernel a)
    at hadd
  change curveEulerCharacteristic f L - curveEulerCharacteristic f (structureModule X) = _
  rw [hadd, add_sub_cancel_left, curveEulerCharacteristic]
  simp only [Module.finrank_zero_of_subsingleton, Nat.cast_zero, sub_zero, a]

/-- A nonzero section forces nonnegative degree. -/
theorem line_degree_nonneg_of_nonzero_section (hd : topologicalKrullDim X ≤ 1)
    {L : X.Modules} (hL : LocallyFreeRankOne L) (s : Γ(L, ⊤)) (hs : s ≠ 0) :
    0 ≤ curveSheafDegree f L := by
  rw [line_degree_eq_section_cokernel_h0 f hd hL s hs]
  exact Nat.cast_nonneg _

/-- Every global section of a negative-degree line vanishes. -/
theorem section_eq_zero_of_line_degree_neg (hd : topologicalKrullDim X ≤ 1)
    {L : X.Modules} (hL : LocallyFreeRankOne L) (hdeg : curveSheafDegree f L < 0)
    (s : Γ(L, ⊤)) : s = 0 := by
  by_contra hs
  exact (not_le_of_gt hdeg) (line_degree_nonneg_of_nonzero_section f hd hL s hs)

/-- A nonzero section of a degree-zero line gives the actual trivialization map. -/
theorem globalSectionHom_isIso_of_degree_zero (hd : topologicalKrullDim X ≤ 1)
    {L : X.Modules} (hL : LocallyFreeRankOne L) (s : Γ(L, ⊤)) (hs : s ≠ 0)
    (hdeg : curveSheafDegree f L = 0) : IsIso (globalSectionHom L s) := by
  have := Chow.source_isNoetherian f
  have := hL.isFinitePresentation
  have := (structureModule_locallyFreeRankOne (X := X)).isFinitePresentation
  let a := globalSectionHom L s
  have := nonzero_globalSectionHom_mono hL s hs
  have := coherent_cokernel a
  have hfin := nonzero_globalSectionHom_cokernel_finiteSupport f hd hL s hs
  have hz : IsZero (cokernel a) := by
    by_contra hn
    have hp := finiteSupport_h0_pos f (cokernel a) hfin hn
    have he := line_degree_eq_section_cokernel_h0 f hd hL s hs
    change curveSheafDegree f L = (Module.finrank k (ModuleScalarH f (cokernel a) 0) : ℤ) at he
    omega
  have : Epi a := Abelian.epi_of_cokernel_π_eq_zero a (hz.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi a

end FLT.Mazur.FCurve
