/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdicCompletionPositiveLimit
public import FLT.Mazur.AffineSeparatedFamilyExt

/-!
# Every original adic stage detects maps to a separated target

Positive quotient evaluations jointly detect all sections of the completion.
The separated equalizer then promotes equality at every finite order to an
actual scheme-morphism equality, retaining nilpotents and original scalars.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.AdicCompletionSeparatedExt
universe u
variable {A : Type u} [CommRing A] (I : Ideal A)
local notation "C" => AdicCompletion I A
local notation "d" m => Spec.map
  (CommRingCat.ofHom (AlgHom.toRingHom (AdicCompletion.evalₐ I (m + 1))))

/-- The actual positive-stage maps jointly detect zero global sections of the completion. -/
theorem sections_detect (x : Γ(Spec (.of (C)), ⊤))
    (hx : ∀ m : ℕ, (d m).appTop x = 0) : x = 0 := by
  apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of (C))).hom).1
  rw [map_zero]
  apply (AdicCompletionPositiveLimit.equivalence I).injective
  apply Subtype.ext
  funext m
  change AdicCompletion.evalₐ I (m + 1) ((Scheme.ΓSpecIso (.of (C))).hom x) = 0
  have hn := congrArg (fun k ↦ k x) (Scheme.ΓSpecIso_naturality
    (CommRingCat.ofHom (AdicCompletion.evalₐ I (m + 1)).toRingHom))
  change (Scheme.ΓSpecIso (.of (A ⧸ I ^ (m + 1)))).hom ((d m).appTop x) =
    AdicCompletion.evalₐ I (m + 1) ((Scheme.ΓSpecIso (.of (C))).hom x) at hn
  rw [← hn, hx, map_zero]

/-- Equality on all actual positive thickenings proves equality over a separated target. -/
theorem hom_ext {Y S : Scheme.{u}} (s : Y ⟶ S) [IsSeparated s]
    {f g : Spec (.of (C)) ⟶ Y} (h : f ≫ s = g ≫ s)
    (he : ∀ m : ℕ, (d m) ≫ f = (d m) ≫ g) : f = g :=
  AffineSeparatedFamilyExt.hom_ext s h (fun m : ℕ ↦ Spec (.of (A ⧸ I ^ (m + 1))))
    (fun m ↦ d m) (sections_detect I) he

end FLT.Mazur.AdicCompletionSeparatedExt
