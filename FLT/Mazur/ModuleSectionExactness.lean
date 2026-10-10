/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleCohomologyRing

/-!
# Global sections and vanishing in a short exact sequence

The actual section maps are exact at the middle term. Vanishing of the
first H1 makes the quotient section map surjective, while vanishing of
both outer cohomology groups forces vanishing of the middle group.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace FLT.Mazur.FCurve

set_option backward.isDefEq.respectTransparency false

local instance sectionExactHasExt (X : Scheme.{u}) :
    HasExt.{u + 1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
  HasExt.standard _

variable {X : Scheme.{u}} (S : ShortComplex X.Modules) (hS : S.ShortExact)

include hS

/-- Exactness of actual global sections at the middle coefficient. -/
theorem moduleSections_exact : Function.Exact (S.f.app ⊤) (S.g.app ⊤) := by
  have he : Function.Exact (moduleHMap S.f 0) (moduleHMap S.g 0) :=
    (ShortComplex.ab_exact_iff_function_exact _).mp
      (Sheaf.H.longSequence_exact₂' (CoherentDevissage.moduleToSheaf_shortExact hS) 0)
  intro s
  constructor
  · intro hs
    have hz : moduleHMap S.g 0 ((moduleH0Equiv S.X₂).symm s) = 0 := by
      apply (moduleH0Equiv S.X₃).injective
      rw [moduleH0Equiv_naturality, LinearEquiv.apply_symm_apply, hs, map_zero]
    obtain ⟨t, ht⟩ := (he _).mp hz
    exact ⟨moduleH0Equiv S.X₁ t, (moduleH0Equiv_naturality S.f t).symm.trans
      ((congrArg (moduleH0Equiv S.X₂) ht).trans
        ((moduleH0Equiv S.X₂).apply_symm_apply s))⟩
  · rintro ⟨t, rfl⟩
    exact congr($(S.zero).app ⊤ t)

/-- Kernel H1 vanishing lifts global sections through the original quotient map. -/
theorem moduleSections_surjective_of_h1
    (hv : Subsingleton (ModuleH S.X₁ 1)) : Function.Surjective (S.g.app ⊤) := by
  have he : Function.Exact (moduleHMap S.g 0)
      (moduleHConnecting S (CoherentDevissage.moduleToSheaf_shortExact hS) 0) :=
    (ShortComplex.ab_exact_iff_function_exact _).mp
      (Sheaf.H.longSequence_exact₃' (CoherentDevissage.moduleToSheaf_shortExact hS) 0 1 rfl)
  intro s
  obtain ⟨t, ht⟩ := (he ((moduleH0Equiv S.X₃).symm s)).mp (hv.elim _ _)
  exact ⟨moduleH0Equiv S.X₂ t, (moduleH0Equiv_naturality S.g t).symm.trans
    ((congrArg (moduleH0Equiv S.X₃) ht).trans
      ((moduleH0Equiv S.X₃).apply_symm_apply s))⟩

/-- Vanishing of both outer groups implies vanishing of the middle group. -/
theorem moduleH_subsingleton_middle (q : ℕ)
    (h₁ : Subsingleton (ModuleH S.X₁ q)) (h₃ : Subsingleton (ModuleH S.X₃ q)) :
    Subsingleton (ModuleH S.X₂ q) := by
  have he : Function.Exact (moduleHMap S.f q) (moduleHMap S.g q) :=
    (ShortComplex.ab_exact_iff_function_exact _).mp
      (Sheaf.H.longSequence_exact₂' (CoherentDevissage.moduleToSheaf_shortExact hS) q)
  have hz (s : ModuleH S.X₂ q) : s = 0 := by
    obtain ⟨t, rfl⟩ := (he s).mp (h₃.elim _ _)
    rw [h₁.elim t 0, map_zero]
  exact ⟨fun a b ↦ (hz a).trans (hz b).symm⟩

end FLT.Mazur.FCurve
