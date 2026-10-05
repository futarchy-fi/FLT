/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicGradedSequence
public import FLT.Mazur.ModuleCohomologyRing

/-!
# Cohomology of infinitesimal coefficient quotients

Vanishing on the associated-graded coefficients propagates to all finite
quotients. Vanishing in degree one makes adjacent degree-zero transition
maps surjective. The uniform Serre bound needed to supply the graded
vanishing, and the comparison with completed cohomology, remain separate.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open FLT.Mazur.FCurve

universe u

namespace FLT.Mazur.IdealAdicQuotient

local instance adicHasExt (X : Scheme.{u}) :
    HasExt.{u + 1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
  HasExt.standard _

variable {X : Scheme.{u}} [IsLocallyNoetherian X]
  (I : X.IdealSheafData) (M : X.Modules) [M.IsFinitePresentation]

/-- Vanishing of all graded coefficients in one degree gives vanishing of every quotient. -/
theorem quotient_moduleH_subsingleton (q : ℕ)
    (h : ∀ n, Subsingleton (ModuleH (graded I M n) q)) (n : ℕ) :
    Subsingleton (ModuleH (quotient I M n) q) := by
  induction n with
  | zero =>
    exact Sheaf.subsingleton_H_of_isZero
      ((CoherentDevissage.moduleToSheaf X).map_isZero (quotient_zero_isZero I M)) q
  | succ n ih =>
    let S := gradedSequence I M n
    have hAb : (moduleAbelianComplex S).ShortExact :=
      CoherentDevissage.moduleToSheaf_shortExact (gradedSequence_shortExact I M n)
    have he : Function.Exact (moduleHMap S.f q) (moduleHMap S.g q) :=
      (ShortComplex.ab_exact_iff_function_exact _).mp (Sheaf.H.longSequence_exact₂' hAb q)
    have hz (x : ModuleH S.X₂ q) : x = 0 := by
      obtain ⟨y, hy⟩ := (he x).mp (ih.elim _ _)
      rw [(h n).elim y 0, map_zero] at hy
      exact hy.symm
    exact ⟨fun x y ↦ (hz x).trans (hz y).symm⟩

/-- Graded degree-one vanishing makes the actual adjacent H0 reduction surjective. -/
theorem reduction_h0_surjective (n : ℕ)
    (h : Subsingleton (ModuleH (graded I M n) 1)) :
    Function.Surjective (moduleHMap (reduction I M (Nat.le_succ n)) 0) := by
  let S := gradedSequence I M n
  have hAb : (moduleAbelianComplex S).ShortExact :=
    CoherentDevissage.moduleToSheaf_shortExact (gradedSequence_shortExact I M n)
  have he : Function.Exact (moduleHMap S.g 0) (moduleHConnecting S hAb 0) :=
    (ShortComplex.ab_exact_iff_function_exact _).mp
      (Sheaf.H.longSequence_exact₃' hAb 0 1 rfl)
  intro x
  exact (he x).mp (h.elim _ _)

/-- Reduction across any finite number of thickenings is surjective on H0. -/
theorem reduction_h0_surjective_of_le
    (h : ∀ n, Subsingleton (ModuleH (graded I M n) 1))
    {a b : ℕ} (hab : a ≤ b) : Function.Surjective (moduleHMap (reduction I M hab) 0) := by
  induction hab with
  | refl =>
    rw [reduction_refl, moduleHMap_id]
    exact Function.surjective_id
  | @step b hab ih =>
    rw [← reduction_trans I M hab (Nat.le_succ b), moduleHMap_comp]
    exact ih.comp (reduction_h0_surjective I M b (h b))

end FLT.Mazur.IdealAdicQuotient
