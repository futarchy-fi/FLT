/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicCohomologyQuotient
public import FLT.Mazur.IdealAdicFormalComparison

/-!
# Compatible quotients by the cohomology image filtration

The original finite injections assemble to an injection of compatible families.
Its range consists precisely of families whose coordinates lift individually.
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

/-- Compatible quotients of the original cohomology by its actual image filtration. -/
def compatibleImages (q : ℕ) : Submodule R (∀ n : ℕ, imageQuotient ρ I M q n) where
  carrier := {x | ∀ (a b : ℕ) (h : a ≤ b), imageQuotientReduction ρ I M q h (x b) = x a}
  zero_mem' := fun _ _ _ ↦ map_zero _
  add_mem' := by
    intro x y hx hy a b h
    change imageQuotientReduction ρ I M q h (x b + y b) = x a + y a
    rw [map_add, hx a b h, hy a b h]
  smul_mem' := by
    intro r x hx a b h
    change imageQuotientReduction ρ I M q h (r • x b) = r • x a
    rw [map_smul, hx a b h]

/-- The finite image-quotient injections assemble using the original reduction identity. -/
def compatibleImageComparison (q : ℕ) :
    compatibleImages ρ I M q →ₗ[R] compatibleCohomology ρ I M q where
  toFun x := ⟨fun n ↦ imageQuotientComparison ρ I M q n (x.val n), by
    intro a b h
    change moduleHMap (reduction I M h) q _ = _
    rw [imageQuotientComparison_reduction, x.property a b h]⟩
  map_add' x y := by
    apply Subtype.ext
    funext n
    exact map_add (imageQuotientComparison ρ I M q n) (x.val n) (y.val n)
  map_smul' r x := by
    apply Subtype.ext
    funext n
    exact map_smul (imageQuotientComparison ρ I M q n) r (x.val n)

/-- Finite injectivity detects equality of compatible image quotients. -/
theorem compatibleImageComparison_injective (q : ℕ) :
    Function.Injective (compatibleImageComparison ρ I M q) := by
  intro x y h
  apply Subtype.ext
  funext n
  apply imageQuotientComparison_injective ρ I M q n
  exact congrArg (fun z : compatibleCohomology ρ I M q ↦ z.val n) h

/-- Individually liftable coordinates have unique, automatically compatible image lifts. -/
theorem mem_range_compatibleImageComparison_iff (q : ℕ)
    (y : compatibleCohomology ρ I M q) :
    y ∈ LinearMap.range (compatibleImageComparison ρ I M q) ↔
      ∀ n, y.val n ∈ LinearMap.range (imageQuotientComparison ρ I M q n) := by
  constructor
  · rintro ⟨x, rfl⟩ n
    exact ⟨x.val n, rfl⟩
  · intro h
    choose x hx using h
    refine ⟨⟨x, ?_⟩, ?_⟩
    · intro a b hab
      apply imageQuotientComparison_injective ρ I M q a
      rw [← imageQuotientComparison_reduction, hx b, hx a]
      exact y.property a b hab
    · apply Subtype.ext
      funext n
      exact hx n

variable (J : Ideal R)
  (hJ : ∀ (r : R), r ∈ J → ∀ U : X.affineOpens,
    X.presheaf.map U.1.leTop.op (ρ r) ∈ I.ideal U)

/-- Ordinary adic quotients map to the actual image quotients. -/
def adicToImageQuotient (q n : ℕ) :
    (ModuleRingH ρ M q ⧸ (J ^ n • ⊤ : Submodule R (ModuleRingH ρ M q))) →ₗ[R]
      imageQuotient ρ I M q n :=
  (J ^ n • ⊤ : Submodule R (ModuleRingH ρ M q)).mapQ
    (cohomologyImage ρ I M q n) LinearMap.id
    (idealPower_smul_top_le_cohomologyImage ρ I M J hJ q n)

/-- Completion maps to compatible image quotients by its original evaluations. -/
def completionToImages (q : ℕ) :
    AdicCompletion J (ModuleRingH ρ M q) →ₗ[R] compatibleImages ρ I M q where
  toFun x := ⟨fun n ↦ adicToImageQuotient ρ I M J hJ q n (x.val n), by
    intro a b hab
    change imageQuotientReduction ρ I M q hab
      (adicToImageQuotient ρ I M J hJ q b (x.val b)) =
        adicToImageQuotient ρ I M J hJ q a (x.val a)
    have he := x.property hab
    rw [← he]
    induction x.val b using Submodule.Quotient.induction_on with
    | _ z => rfl⟩
  map_add' x y := by
    apply Subtype.ext
    funext n
    exact map_add (adicToImageQuotient ρ I M J hJ q n) (x.val n) (y.val n)
  map_smul' r x := by
    apply Subtype.ext
    funext n
    exact map_smul (adicToImageQuotient ρ I M J hJ q n) r (x.val n)

/-- Factoring through image quotients retains the original formal comparison. -/
lemma compatibleImageComparison_completionToImages (q : ℕ)
    (x : AdicCompletion J (ModuleRingH ρ M q)) :
    compatibleImageComparison ρ I M q (completionToImages ρ I M J hJ q x) =
      formalComparison ρ I M J hJ q x := by
  apply Subtype.ext
  funext n
  change imageQuotientComparison ρ I M q n
    (adicToImageQuotient ρ I M J hJ q n (x.val n)) =
      adicQuotientComparison ρ I M J hJ q n (x.val n)
  induction x.val n using Submodule.Quotient.induction_on with
  | _ z => rfl

end FLT.Mazur.IdealAdicQuotient
