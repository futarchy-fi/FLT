/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.NonzeroSectionPointCondition
public import FLT.Mazur.FiniteIdealConditionDimension
public import FLT.Mazur.CurvePositiveDegreeSections

/-!
# Retaining the rational point in a cohomological point condition

The existing full finite ideal condition recovers an actual rational section
from its quotient isomorphism. This witness can be lifted to the universal
point parameter space, while retaining the exact H⁰ loss and H¹ vanishing.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.FCurve
open ModuleSheafTensor
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] tensor

variable {k : Type} [Field k] {X : Scheme} (f : X ⟶ Spec (.of k))

/-- A full ideal with quotient isomorphic to the base is the kernel of an actual section. -/
theorem exists_section_kernel (I : X.IdealSheafData) [IsIso (I.subschemeι ≫ f)] :
    ∃ p : Spec (.of k) ⟶ X, p ≫ f = 𝟙 _ ∧ p.ker = I := by
  let e := asIso (I.subschemeι ≫ f)
  refine ⟨e.inv ≫ I.subschemeι, ?_, ?_⟩
  · exact e.inv_hom_id
  · rw [Scheme.Hom.ker_comp_of_isIso, Scheme.IdealSheafData.ker_subschemeι]

/-- An actual rational point preserves acyclicity and imposes exactly one condition. -/
theorem exists_rational_point_rank_drop [IsAlgClosed k] [IsReduced X]
    [IsProper f] [SmoothOfRelativeDimension 1 f] {L : X.Modules}
    (hL : LocallyFreeRankOne L) [Subsingleton (ModuleScalarH f L 1)]
    (hp : 0 < Module.finrank k (ModuleScalarH f L 0)) :
    ∃ (p : Spec (.of k) ⟶ X) (_ : p ≫ f = 𝟙 _),
      Subsingleton (ModuleScalarH f (tensor (idealModule p.ker) L) 1) ∧
      Module.finrank k (ModuleScalarH f (tensor (idealModule p.ker) L) 0) + 1 =
        Module.finrank k (ModuleScalarH f L 0) := by
  obtain ⟨s, hs⟩ := exists_nonzero_section_of_h0_pos f L hp
  obtain ⟨I, _, hi, hI⟩ := exists_cartier_point_condition f hL s hs
  let _ := hi
  obtain ⟨p, hp, he⟩ := exists_section_kernel f I
  refine ⟨p, hp, ?_⟩
  rw [he]
  exact idealLine_acyclic_rank_drop_one f I hL s hI

end FLT.Mazur.FCurve
