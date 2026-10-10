/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.StalkBaseSectionNumerator
public import FLT.Mazur.SectionGeneratorScalar

/-!
# Generator opens of stalk-base numerators

A section on the stalk-base family has an original global numerator with
exactly the same generator open after pullback. The denominator is a unit.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules FLT.Mazur.FCurve

namespace FLT.Mazur.StalkBase

variable {X S : Scheme.{0}} [IsAffine S] [CompactSpace X] [X.IsSeparated]
  (f : X ⟶ S) (s : S) {M : X.Modules} [M.IsQuasicoherent]

/-- A local section and an original numerator generate on the same local-base open. -/
theorem exists_section_numerator_open (hM : LocallyFreeRankOne M)
    (t : Γ((pullback (toSource f s)).obj M, ⊤)) :
    ∃ a : Γ(M, ⊤), toSource f s ⁻¹ᵁ sectionGeneratorOpen M a =
      sectionGeneratorOpen ((pullback (toSource f s)).obj M) t := by
  obtain ⟨r, a, ha⟩ := exists_section_numerator f s M t
  refine ⟨a, ?_⟩
  rw [← sectionGeneratorOpen_pullGlobal hM, ha, sectionGeneratorOpen_smul,
    (family f s).basicOpen_of_isUnit (denominator_isUnit f s r), top_inf_eq]

end FLT.Mazur.StalkBase
