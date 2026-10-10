/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicCohomologyScalars
public import Mathlib.RingTheory.AdicCompletion.Basic

/-!
# The canonical comparison from completed cohomology

The scalar containment constructs maps from ordinary adic quotients to the
cohomology of actual coefficient quotients. Their compatibility constructs
the formal comparison map. Bijectivity is the separate formal-functions
assertion, and is not assumed in this construction.
-/

@[expose] public noncomputable section

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

/-- Restriction on cohomology factors through the ordinary base-adic quotient. -/
def adicQuotientComparison (q n : ℕ) :
    (ModuleRingH ρ M q ⧸ (J ^ n • ⊤ : Submodule R (ModuleRingH ρ M q))) →ₗ[R]
      ModuleRingH ρ (quotient I M n) q :=
  (J ^ n • ⊤ : Submodule R (ModuleRingH ρ M q)).liftQ
    ((moduleRingHFunctor ρ q).map (projection I M n)).hom
    ((idealPower_smul_top_le_cohomologyImage ρ I M J hJ q n).trans
      (cohomologyImage_eq_ker ρ I M q n).le)

/-- The finite comparison is induced by the original coefficient restriction. -/
lemma adicQuotientComparison_mk (q n : ℕ) (x : ModuleRingH ρ M q) :
    adicQuotientComparison ρ I M J hJ q n (Submodule.Quotient.mk x) =
      moduleHMap (projection I M n) q x := rfl

/-- Finite comparisons commute with every actual transition map. -/
lemma adicQuotientComparison_reduction (q : ℕ) {a b : ℕ} (h : a ≤ b)
    (x : ModuleRingH ρ M q ⧸ (J ^ b • ⊤ : Submodule R (ModuleRingH ρ M q))) :
    moduleHMap (reduction I M h) q (adicQuotientComparison ρ I M J hJ q b x) =
      adicQuotientComparison ρ I M J hJ q a
        (AdicCompletion.transitionMap J (ModuleRingH ρ M q) h x) := by
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
    change moduleHMap (reduction I M h) q (moduleHMap (projection I M b) q x) =
      moduleHMap (projection I M a) q x
    rw [← LinearMap.comp_apply, ← moduleHMap_comp, projection_reduction]

/-- Compatible classes in the cohomology of all actual coefficient quotients. -/
def compatibleCohomology (q : ℕ) :
    Submodule R (∀ n : ℕ, ModuleRingH ρ (quotient I M n) q) where
  carrier := {x | ∀ (a b : ℕ) (h : a ≤ b),
    ((moduleRingHFunctor ρ q).map (reduction I M h)).hom (x b) = x a}
  zero_mem' := fun _ _ _ ↦ map_zero _
  add_mem' := by
    intro x y hx hy a b h
    change ((moduleRingHFunctor ρ q).map (reduction I M h)).hom
      (x b + y b) = x a + y a
    rw [map_add, hx a b h, hy a b h]
  smul_mem' := by
    intro r x hx a b h
    change ((moduleRingHFunctor ρ q).map (reduction I M h)).hom (r • x b) = r • x a
    rw [map_smul, hx a b h]

/-- Completed original cohomology maps canonically to compatible quotient cohomology. -/
def formalComparison (q : ℕ) :
    AdicCompletion J (ModuleRingH ρ M q) →ₗ[R] compatibleCohomology ρ I M q where
  toFun x := ⟨fun n ↦ adicQuotientComparison ρ I M J hJ q n (x.val n), by
    intro a b h
    change moduleHMap (reduction I M h) q _ = _
    rw [adicQuotientComparison_reduction, AdicCompletion.transitionMap_comp_eval_apply]⟩
  map_add' x y := by
    apply Subtype.ext
    funext n
    exact map_add (adicQuotientComparison ρ I M J hJ q n) (x.val n) (y.val n)
  map_smul' r x := by
    apply Subtype.ext
    funext n
    exact map_smul (adicQuotientComparison ρ I M J hJ q n) r (x.val n)

/-- Every component of the comparison uses the canonical completion evaluation. -/
lemma formalComparison_eval (q n : ℕ) (x : AdicCompletion J (ModuleRingH ρ M q)) :
    (formalComparison ρ I M J hJ q x).val n =
      adicQuotientComparison ρ I M J hJ q n
        (AdicCompletion.eval J (ModuleRingH ρ M q) n x) := rfl

/-- The formal comparison extends the actual restrictions of original cohomology. -/
lemma formalComparison_of (q n : ℕ) (x : ModuleRingH ρ M q) :
    (formalComparison ρ I M J hJ q (AdicCompletion.of J (ModuleRingH ρ M q) x)).val n =
      moduleHMap (projection I M n) q x := rfl

end FLT.Mazur.IdealAdicQuotient
