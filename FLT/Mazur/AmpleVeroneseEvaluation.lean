/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AmpleGlobalGeneration

/-!
# Finite ample evaluations in a prescribed Veronese

Raise a finite common-degree section cover to a prescribed positive power.
Its generator opens are unchanged, so the resulting finite evaluation is
still epimorphic and its degree is a multiple of the prescribed step.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Scheme.Modules

universe u

namespace FLT.Mazur.FCurve

open ProjectiveSpace ModuleLineBundleTensorPullback

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {X : Scheme.{u}} {L : X.Modules}

/-- A finite generating family can be chosen in a positive multiple of any positive step. -/
theorem AmpleLineBundle.exists_multiple_finite_evaluation (hL : AmpleLineBundle L)
    (q : ℕ) (hq : 0 < q) :
    ∃ a : ℕ, 0 < a ∧ ∃ (I : Type u) (_ : Finite I)
      (s : I → Γ(tensorPower L (q * a), ⊤)),
      Epi (globalEvaluation (tensorPower L (q * a)) s) := by
  obtain ⟨I, hI, a, ha, s, _, hcover⟩ := hL.common_degree_section_cover
  let e := tensorPowerMulIso L a q ≪≫ eqToIso (congrArg (tensorPower L) (Nat.mul_comm a q))
  let t (i : I) := e.hom.app ⊤ (tensorPowerSection (tensorPower L a) ⊤ (s i) q)
  have hopen (i : I) : sectionGeneratorOpen (tensorPower L (q * a)) (t i) =
      sectionGeneratorOpen (tensorPower L a) (s i) := by
    exact (sectionGeneratorOpen_iso e _).trans
      (tensorPowerSection_generatorOpen (hL.2.1.tensorPower a) (s i) hq)
  refine ⟨a, ha, I, hI, t, ?_⟩
  apply globalEvaluation_epi_of_sectionHom_isIso t
    (fun i ↦ sectionGeneratorOpen (tensorPower L (q * a)) (t i))
    ((iSup_congr hopen).trans hcover) id
  intro i
  exact sectionHom_generatorOpen_isIso (tensorPower L (q * a)) (t i)

end FLT.Mazur.FCurve
