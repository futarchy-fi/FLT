/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeRelationNilpotentSections
public import Mathlib.Topology.Sheaves.Stalks

/-!
# Nilpotence on arbitrary source neighborhoods

The explicit exponent of a scheme-theoretic kernel controls every section
killed by restriction, even on nonaffine opens. Affine neighborhoods are used
only to check the equation, and the sheaf condition glues the zero equality.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
universe u
namespace FLT.Mazur.NilpotentSectionRestriction
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y : Scheme.{u}} (g : X ⟶ Y) [QuasiCompact g]
  (n : ℕ) (hn : g.ker ^ n = ⊥)
include hn

/-- The source kernel bound annihilates every restricted affine section. -/
theorem affine_pow_eq_zero (U : Y.Opens) (hU : IsAffineOpen U)
    (s : Γ(Y, U)) (hs : g.app U s = 0) : s ^ n = 0 := by
  have he := congrArg (fun J : Y.IdealSheafData ↦ J.ideal ⟨U, hU⟩) hn
  have hk : RingHom.ker (g.app U).hom ^ n = ⊥ := by
    simpa only [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply, Scheme.Hom.ker_apply,
      Scheme.IdealSheafData.ideal_bot, Pi.bot_apply] using he
  have hm := Ideal.pow_mem_pow (I := RingHom.ker (g.app U).hom) hs n
  rw [hk] at hm
  exact hm

/-- The same exponent works on every open, with no affine-neighborhood condition on the quotient. -/
theorem pow_eq_zero (U : Y.Opens) (s : Γ(Y, U)) (hs : g.app U s = 0) : s ^ n = 0 := by
  apply TopCat.Presheaf.section_ext Y.toSheafedSpace.sheaf U
  intro y hy
  change Y.presheaf.germ U y hy (s ^ n) = Y.presheaf.germ U y hy 0
  obtain ⟨_, ⟨(V : Y.Opens), hV, rfl⟩, hyV, hVU : V ≤ U⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open hy U.isOpen
  let v := Y.presheaf.map (homOfLE hVU).op s
  have hv : g.app V v = 0 := by
    have he := congrArg (fun k ↦ k s) (g.naturality (homOfLE hVU).op)
    change g.app V v = X.presheaf.map _ (g.app U s) at he
    exact he.trans (by rw [hs, map_zero])
  have hz : v ^ n = 0 := affine_pow_eq_zero g n hn V hV v hv
  have hr : Y.presheaf.map (homOfLE hVU).op (s ^ n) = 0 := by
    rw [map_pow]
    exact hz
  rw [← Y.presheaf.germ_res_apply (homOfLE hVU) y hyV, hr, map_zero, map_zero]

end FLT.Mazur.NilpotentSectionRestriction
