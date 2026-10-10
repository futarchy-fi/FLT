/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ClosedFiberTensorExactness
public import FLT.Mazur.ArtinianProperRelativeFunctions
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
# Artinian functions from connected reduced closed fibers

The actual structural pullback is bijective when the actual residue-quotient
fibers are connected and reduced. Over a local Artinian ring this asks only
about its single closed fiber, with no assumption on geometric fibers.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
namespace FLT.Mazur.ArtinianClosedFiberFunctions
open Chow ArtinianSectionKernel ArtinianRelativeSectionCriterion
open AffineBaseChangeCoefficients
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {X S : Scheme} (f : X ⟶ S) [IsAffine S] [IsArtinianRing Γ(S, ⊤)]
  [IsProper f] [Flat f] (s : S ⟶ X) (hs : s ≫ f = 𝟙 S)

include s hs

/-- All closed fibers suffice for the Artinian structural comparison. -/
theorem appTop_bijective
    (hc : ∀ (I : Ideal Γ(S, ⊤)), I.IsMaximal →
      ConnectedSpace ↥(pullback f (baseMap S (Γ(S, ⊤) ⧸ I))))
    (hr : ∀ (I : Ideal Γ(S, ⊤)), I.IsMaximal →
      IsReduced (pullback f (baseMap S (Γ(S, ⊤) ⧸ I)))) :
    Function.Bijective f.appTop := by
  let _ : X.IsSeparated := ⟨by rw [← terminal.comp_from f]; infer_instance⟩
  let _ := QuasiCompact.compactSpace_of_compactSpace f
  let C := X.affineCover.finiteSubcover
  let U : C.I₀ → X.Opens := fun i ↦ (C.f i).opensRange
  have hA (i : C.I₀) : IsAffineOpen (U i) := isAffineOpen_opensRange (C.f i)
  apply ArtinianRelativeSectionCriterion.appTop_bijective f U C.iSup_opensRange hA s hs
  intro I hI
  let _ := hc I hI
  let _ := hr I hI
  exact ClosedFiberTensorExactness.residue_exact f U C.iSup_opensRange hA s hs I

/-- A local Artinian family needs only its one actual connected reduced closed fiber. -/
theorem local_appTop_bijective [IsLocalRing Γ(S, ⊤)]
    [ConnectedSpace ↥(pullback f (baseMap S (Γ(S, ⊤) ⧸ IsLocalRing.maximalIdeal Γ(S, ⊤))))]
    [IsReduced (pullback f (baseMap S (Γ(S, ⊤) ⧸ IsLocalRing.maximalIdeal Γ(S, ⊤))))] :
    Function.Bijective f.appTop := by
  apply appTop_bijective f s hs
  · intro I hI
    rw [IsLocalRing.eq_maximalIdeal hI]
    infer_instance
  · intro I hI
    rw [IsLocalRing.eq_maximalIdeal hI]
    infer_instance

/-- The inverse of structural pullback is the original section evaluation. -/
theorem local_evaluation_injective [IsLocalRing Γ(S, ⊤)]
    [ConnectedSpace ↥(pullback f (baseMap S (Γ(S, ⊤) ⧸ IsLocalRing.maximalIdeal Γ(S, ⊤))))]
    [IsReduced (pullback f (baseMap S (Γ(S, ⊤) ⧸ IsLocalRing.maximalIdeal Γ(S, ⊤))))] :
    Function.Injective s.appTop := by
  have H := local_appTop_bijective f s hs
  have he := SchemeRelativeNilpotentSections.evaluation_pullback f s hs
  intro x y h
  obtain ⟨a, rfl⟩ := H.surjective x
  obtain ⟨b, rfl⟩ := H.surjective y
  rw [he, he] at h
  exact congrArg f.appTop h

end FLT.Mazur.ArtinianClosedFiberFunctions
