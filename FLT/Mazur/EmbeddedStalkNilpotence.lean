/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.Geometry.RingedSpace.Stalks
public import Mathlib.Topology.Sheaves.CommRingCat

/-!
# Nilpotence in stalks of an embedded ringed subspace

A uniform power bound for kernels on open sections gives the same bound for
the kernel at every stalk. The inducing topology supplies an ambient open on
which an equality of source germs is an equality of restricted sections.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
universe u
namespace FLT.Mazur.EmbeddedStalkNilpotence
set_option backward.isDefEq.respectTransparency false
variable {X Y : PresheafedSpace CommRingCat.{u}} (f : X ⟶ Y)
  (hf : Topology.IsInducing f.base) (n : ℕ)
  (hsec : ∀ (U : Opens Y) (a : Y.presheaf.obj (op U)),
    f.c.app (op U) a = 0 → a ^ n = 0)
include hf hsec

/-- A section kernel bound passes to every stalk without any surjectivity assumption. -/
theorem pow_eq_zero (x : X) (a : Y.presheaf.stalk (f.base x))
    (ha : f.stalkMap x a = 0) : a ^ n = 0 := by
  obtain ⟨U, hxU, b, rfl⟩ := Y.presheaf.exists_germ_eq a
  rw [PresheafedSpace.stalkMap_germ_apply] at ha
  have hg : X.presheaf.germ ((Opens.map f.base).obj U) x hxU
      (f.c.app (op U) b) =
      X.presheaf.germ ((Opens.map f.base).obj U) x hxU 0 := by
    exact ha.trans (map_zero _).symm
  obtain ⟨V, hxV, iV, _, hV⟩ := X.presheaf.germ_eq x hxU hxU _ _ hg
  rw [map_zero] at hV
  obtain ⟨W₀, hW₀, he⟩ := hf.isOpen_iff.mp V.isOpen
  let W : Opens Y := U ⊓ ⟨W₀, hW₀⟩
  have hxW : f.base x ∈ W := ⟨hxU, by change x ∈ f.base ⁻¹' W₀; rwa [he]⟩
  have hWV : (Opens.map f.base).obj W ≤ V := by
    intro z hz
    exact (Set.ext_iff.mp he z).mp hz.2
  let j : W ⟶ U := homOfLE inf_le_left
  let k : (Opens.map f.base).obj W ⟶ V := homOfLE hWV
  have hz : f.c.app (op W) (Y.presheaf.map j.op b) = 0 := by
    have ht := congrArg (fun v ↦ v b) (f.c.naturality j.op)
    change f.c.app (op W) (Y.presheaf.map j.op b) =
      X.presheaf.map ((Opens.map f.base).map j).op (f.c.app (op U) b) at ht
    refine ht.trans ?_
    have hi : ((Opens.map f.base).map j).op = iV.op ≫ k.op := Subsingleton.elim _ _
    rw [hi, X.presheaf.map_comp, ConcreteCategory.comp_apply, hV, map_zero]
  have hb := hsec W (Y.presheaf.map j.op b) hz
  have hr := Y.presheaf.germ_res_apply j (f.base x) hxW b
  rw [← hr, ← map_pow, hb, map_zero]

end FLT.Mazur.EmbeddedStalkNilpotence
