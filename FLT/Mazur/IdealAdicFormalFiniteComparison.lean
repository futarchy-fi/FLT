/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicFormalComparison

/-!
# Passing finite comparison isomorphisms to compatible families

Bijective finite comparisons supply unique lifts of every coordinate. Their
original transition identity proves compatibility of those lifts.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.FCurve

universe u

namespace FLT.Mazur.IdealAdicQuotient

variable {X : Scheme.{u}} [IsLocallyNoetherian X]
  {R : Type u} [CommRing R] (ρ : R →+* Γ(X, ⊤))
  (I : X.IdealSheafData) (M : X.Modules) [M.IsFinitePresentation]
  (J : Ideal R)
  (hJ : ∀ (r : R), r ∈ J → ∀ U : X.affineOpens,
    X.presheaf.map U.1.leTop.op (ρ r) ∈ I.ideal U)

/-- Bijective finite comparisons make the original comparison on compatible families bijective. -/
theorem formalComparison_bijective_of_finite (q : ℕ)
    (h : ∀ n, Function.Bijective (adicQuotientComparison ρ I M J hJ q n)) :
    Function.Bijective (formalComparison ρ I M J hJ q) := by
  constructor
  · intro x y hxy
    apply AdicCompletion.ext
    intro n
    apply (h n).1
    exact congrArg (fun z : compatibleCohomology ρ I M q ↦ z.val n) hxy
  · intro y
    choose x hx using fun n ↦ (h n).2 (y.val n)
    have hc : ∀ {a b : ℕ} (hab : a ≤ b),
        AdicCompletion.transitionMap J (ModuleRingH ρ M q) hab (x b) = x a := by
      intro a b hab
      apply (h a).1
      rw [← adicQuotientComparison_reduction, hx b, hx a]
      exact y.property a b hab
    refine ⟨⟨x, hc⟩, ?_⟩
    apply Subtype.ext
    funext n
    exact hx n

end FLT.Mazur.IdealAdicQuotient
