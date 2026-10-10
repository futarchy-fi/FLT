/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AmpleVeroneseEvaluation

/-!
# Affine section covers in prescribed retained degrees

Taking positive powers keeps the original generator opens. Consequently an
ample line has a finite affine generator cover in a positive multiple of
any prescribed positive step, on the entire original scheme.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Scheme.Modules

universe u

namespace FLT.Mazur.FCurve

open ModuleLineBundleTensorPullback

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {X : Scheme.{u}} {L : X.Modules}

/-- A finite affine generator cover can be chosen in any positive retained sequence of degrees. -/
theorem AmpleLineBundle.retained_section_cover (hL : AmpleLineBundle L)
    (q : ℕ) (hq : 0 < q) :
    ∃ (I : Type u) (_ : Finite I) (d : ℕ) (_ : 0 < d)
      (s : I → Γ(tensorPower L (q * d), ⊤)),
      (∀ i, IsAffineOpen (sectionGeneratorOpen (tensorPower L (q * d)) (s i))) ∧
      ⨆ i, sectionGeneratorOpen (tensorPower L (q * d)) (s i) = ⊤ := by
  obtain ⟨I, hI, d, hd, s, haff, hcover⟩ := hL.common_degree_section_cover
  let e := tensorPowerMulIso L d q ≪≫ eqToIso (congrArg (tensorPower L) (Nat.mul_comm d q))
  let t (i : I) := e.hom.app ⊤ (tensorPowerSection (tensorPower L d) ⊤ (s i) q)
  have hopen (i : I) : sectionGeneratorOpen (tensorPower L (q * d)) (t i) =
      sectionGeneratorOpen (tensorPower L d) (s i) := by
    exact (sectionGeneratorOpen_iso e _).trans
      (tensorPowerSection_generatorOpen (hL.2.1.tensorPower d) (s i) hq)
  refine ⟨I, hI, d, hd, t, ?_, ?_⟩
  · intro i
    rw [hopen]
    exact haff i
  · exact (iSup_congr hopen).trans hcover

end FLT.Mazur.FCurve
