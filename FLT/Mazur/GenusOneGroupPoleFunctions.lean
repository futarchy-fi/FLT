/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DivisorComplementLinear
public import FLT.Mazur.GenusOneGroupPointPowers

/-!
# Actual functions of exact pole order on geometric genus-one group curves

The strict growth of the original point's pole spaces constructs new functions
on its actual complement. In particular orders two and three are available
without choosing or assuming any Weierstrass equation.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.FCurve
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {k : Type} [Field k] [IsAlgClosed k]
  (G : Over (Spec (.of k))) [GrpObj G] [IsIntegral G.left] [IsProper G.hom]
  [SmoothOfRelativeDimension 1 G.hom]
  (hd : topologicalKrullDim G.left = 1) (hc : HasConstantGlobalSections G.hom)
  (hg : curveGenus G.hom hd hc = 1)
  (s : 𝟙_ (Over (Spec (.of k))) ⟶ G) (hI : EffectiveCartier s.left.ker)

include hg

/-- The actual complement-function pole space has the expected positive dimension. -/
theorem genusOne_group_pole_finrank (m : ℕ) (hm : 0 < m) :
    Module.finrank k (divisorPoleSubmodule G.hom hI m) = m := by
  rw [divisorPoleSubmodule_finrank]
  exact genusOne_group_pointPower_h0 G hd hc hg s hI m hm

/-- Every positive pole step strictly enlarges the original space of functions. -/
theorem genusOne_group_pole_lt_succ (m : ℕ) (hm : 0 < m) :
    divisorPoleSubmodule G.hom hI m < divisorPoleSubmodule G.hom hI (m + 1) := by
  apply lt_of_le_of_ne (divisorPoleSubmodule_mono G.hom hI (Nat.le_succ m))
  intro he
  have hr := congrArg (fun Q : Submodule k (divisorComplementModule G.hom s.left.ker) ↦
    Module.finrank k Q) he
  rw [genusOne_group_pole_finrank G hd hc hg s hI m hm,
    genusOne_group_pole_finrank G hd hc hg s hI (m + 1) (by omega)] at hr
  omega

/-- A function of each exact order at least two exists on the original complement. -/
theorem genusOne_group_exists_pole_function (m : ℕ) (hm : 0 < m) :
    ∃ z : divisorComplementModule G.hom s.left.ker,
      z ∈ divisorPoleSubmodule G.hom hI (m + 1) ∧ z ∉ divisorPoleSubmodule G.hom hI m :=
  IsConcreteLE.exists_of_lt (genusOne_group_pole_lt_succ G hd hc hg s hI m hm)

/-- Choose the actual function, keeping the original complement and base-field scalars. -/
def genusOneGroupPoleFunction (m : ℕ) (hm : 0 < m) :
    divisorComplementModule G.hom s.left.ker :=
  (genusOne_group_exists_pole_function G hd hc hg s hI m hm).choose

/-- The chosen function has the asserted upper bound and no smaller bound. -/
theorem genusOneGroupPoleFunction_spec (m : ℕ) (hm : 0 < m) :
    genusOneGroupPoleFunction G hd hc hg s hI m hm ∈
        divisorPoleSubmodule G.hom hI (m + 1) ∧
      genusOneGroupPoleFunction G hd hc hg s hI m hm ∉ divisorPoleSubmodule G.hom hI m :=
  (genusOne_group_exists_pole_function G hd hc hg s hI m hm).choose_spec

/-- The chosen functions are nonzero as actual regular functions. -/
theorem genusOneGroupPoleFunction_ne_zero (m : ℕ) (hm : 0 < m) :
    genusOneGroupPoleFunction G hd hc hg s hI m hm ≠ 0 := by
  intro hz
  apply (genusOneGroupPoleFunction_spec G hd hc hg s hI m hm).2
  rw [hz]
  exact (divisorPoleSubmodule G.hom hI m).zero_mem

end FLT.Mazur.FCurve
