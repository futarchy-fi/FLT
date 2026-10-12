/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteFieldRankLength
public import FLT.Mazur.SectionSumFieldLength

/-!
# Length-one finite divisors are rational points

The actual finite structure map of a divisor of field length one is an
isomorphism. Its inverse constructs a rational section with exactly the original
ideal, including the closed subscheme structure.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.FCurve

variable {k : Type} [Field k] {X : Scheme} (f : X ⟶ Spec (.of k))

/-- A finite scheme of field length one is the original base field. -/
theorem isIso_of_finiteSchemeLength_one [IsFinite f] (h : finiteSchemeLength f = 1) :
    IsIso f := by
  apply (Scheme.Hom.isIso_iff_finrank_eq f).mpr
  funext s
  exact (finrank_eq_finiteSchemeLength f s).trans h

/-- Length one characterizes an actual rational-point divisor, not merely its support. -/
theorem divisorFieldLength_one_iff_section [IsSeparated f] (I : X.IdealSheafData)
    [IsFinite (I.subschemeι ≫ f)] :
    divisorFieldLength f I = 1 ↔
      ∃ s : Spec (.of k) ⟶ X, s ≫ f = 𝟙 _ ∧ s.ker = I := by
  constructor
  · intro h
    let q := I.subschemeι ≫ f
    have : IsIso q := isIso_of_finiteSchemeLength_one q h
    refine ⟨inv q ≫ I.subschemeι, ?_, ?_⟩
    · exact Category.assoc _ _ _ |>.trans (IsIso.inv_hom_id q)
    · rw [Scheme.Hom.ker_comp_of_isIso, I.ker_subschemeι]
  · rintro ⟨s, hs, rfl⟩
    exact divisorFieldLength_section f s hs

end FLT.Mazur.FCurve
