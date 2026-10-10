/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AmpleCommonDegree

/-!
# Finite affine section covers above a prescribed degree

A common-degree ample section cover can be raised to a positive power
without changing any of its generator opens. Its degree can therefore be
chosen beyond a section-lifting or cohomology-vanishing bound.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry

universe u

namespace FLT.Mazur.FCurve

open ModuleLineBundleTensorPullback

/-- An ample line has a finite affine section cover in a positive degree above any bound. -/
theorem AmpleLineBundle.high_degree_section_cover {X : Scheme.{u}} {L : X.Modules}
    (hL : AmpleLineBundle L) (N : ℕ) :
    ∃ (n : ℕ), N ≤ n ∧ 0 < n ∧ ∃ (ι : Type u) (_ : Finite ι)
      (s : ι → Γ(tensorPower L n, ⊤)),
      (∀ i, IsAffineOpen (sectionGeneratorOpen (tensorPower L n) (s i))) ∧
      (⨆ i, sectionGeneratorOpen (tensorPower L n) (s i)) = ⊤ := by
  obtain ⟨ι, hι, n, hn, s, haff, hcover⟩ := hL.common_degree_section_cover
  let e := tensorPowerMulIso L n (N + 1)
  let t (i : ι) := e.hom.app ⊤ (tensorPowerSection (tensorPower L n) ⊤ (s i) (N + 1))
  have hopen (i : ι) : sectionGeneratorOpen (tensorPower L (n * (N + 1))) (t i) =
      sectionGeneratorOpen (tensorPower L n) (s i) := by
    exact (sectionGeneratorOpen_iso e _).trans
      (tensorPowerSection_generatorOpen (hL.2.1.tensorPower n) (s i) (Nat.succ_pos N))
  have hge : N + 1 ≤ n * (N + 1) := by
    exact (one_mul (N + 1)).symm.trans_le (Nat.mul_le_mul_right (N + 1) hn)
  exact ⟨n * (N + 1), by omega, Nat.mul_pos hn (Nat.succ_pos N), ι, hι, t,
    fun i ↦ (hopen i).symm ▸ haff i, (iSup_congr hopen).trans hcover⟩

end FLT.Mazur.FCurve
