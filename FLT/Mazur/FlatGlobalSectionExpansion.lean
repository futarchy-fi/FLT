/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FlatGlobalSectionBaseChange
public import FLT.Mazur.ModuleGlobalSectionPullback
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness

/-!
# Finite expansions of sections after flat base change

Each section upstairs is a finite linear combination, over the new base ring,
of pullbacks of actual global sections downstairs.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite TensorProduct
open Scheme.Modules
namespace FLT.Mazur.FlatGlobalSectionExpansion
open FCurve OpenModuleSectionScalars FlatGlobalSectionBaseChange
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {P X T S : Scheme} [CompactSpace X] [X.IsSeparated] [IsAffine T] [IsAffine S]
  {p : P ⟶ X} {q : P ⟶ T} {f : X ⟶ S} {g : T ⟶ S} [Flat g]
  (h : IsPullback p q f g) (M : X.Modules) [M.IsQuasicoherent]

include h in
/-- Every global section after base change has a finite expansion by pulled-back sections. -/
theorem exists_sum_pullGlobal (s : openSections q ((pullback p).obj M) ⊤) :
    ∃ t : Finset (Γ(T, ⊤) × openSections f M ⊤),
      s = ∑ a ∈ t, a.1 •
        (show openSections q ((pullback p).obj M) ⊤ from pullGlobal p M a.2) := by
  let : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
  obtain ⟨t, ht⟩ := TensorProduct.exists_finset ((sectionsIso h M).inv s)
  refine ⟨t, ?_⟩
  have he := congrArg (fun x ↦ (sectionsIso h M).hom x) ht
  rw [← ConcreteCategory.comp_apply, (sectionsIso h M).inv_hom_id] at he
  simp only [ConcreteCategory.id_apply, map_sum, sectionsIso_tmul] at he
  exact he

end FLT.Mazur.FlatGlobalSectionExpansion
