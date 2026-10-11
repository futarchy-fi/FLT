/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalClosedCohomology
public import FLT.Mazur.IdealAdicLineQuotient
public import FLT.Mazur.LineScalarMonicity
public import FLT.Mazur.PrincipalSectionExtension

/-!
# Nakayama vanishing for an actual line over a principal closed fiber

The regular scalar quotient of a line is the pushed-forward closed pullback.
Its cohomology therefore controls the original finite cohomology by Nakayama.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FLT.Mazur.PrincipalClosedLineCohomology

open FCurve IdealPowerScalarLift

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] GlobalIdealPower.inclusion IdealPowerScalarLift.scalarEnd
  Scheme.Modules.pullback Scheme.Modules.pushforward

variable {X : Scheme.{0}} [IsLocallyNoetherian X]
  (I : X.IdealSheafData) (L : X.Modules) (hL : LocallyFreeRankOne L)
  (r : Γ(X, ⊤))
  (hI : ∀ U : X.affineOpens, I.ideal U =
    Ideal.span {X.presheaf.map U.1.leTop.op r})
  [Mono (scalarEnd (structureModule X) r)]

/-- The actual regular scalar quotient of a line is its original closed restriction. -/
def cokernelIso : cokernel (scalarEnd L r) ≅
    (Scheme.Modules.pushforward I.subschemeι).obj
      ((Scheme.Modules.pullback I.subschemeι).obj L) := by
  let _ := hL.isFinitePresentation
  let _ := LineScalarMonicity.scalarEnd_mono L r hL
  let e : cokernel (GlobalIdealPower.inclusion I L) ≅
      (Scheme.Modules.pushforward I.subschemeι).obj
        ((Scheme.Modules.pullback I.subschemeι).obj L) := by
    have e := IdealAdicQuotient.lineQuotientClosedIso I L hL 1
    change cokernel (GlobalIdealPower.inclusion (I ^ 1) L) ≅ _ at e
    rw [pow_one] at e
    exact e
  exact (RegularPrincipalStructureQuotient.cokernelIso I L r hI).trans e

/-- Scalar quotient cohomology is the cohomology of the actual closed line. -/
def quotientEquiv [X.IsSeparated] {R : Type} [CommRing R]
    (ρ : R →+* Γ(X, ⊤)) (q : ℕ) :
    ModuleRingH ρ (cokernel (scalarEnd L r)) q ≃ₗ[R]
      ModuleRingH (I.subschemeι.appTop.hom.comp ρ)
        ((Scheme.Modules.pullback I.subschemeι).obj L) q := by
  let _ := LocallyOfFiniteType.isLocallyNoetherian I.subschemeι
  let _ := (hL.pullback I.subschemeι).isFinitePresentation
  exact ((moduleRingHFunctor ρ q).mapIso (cokernelIso I L hL r hI)).toLinearEquiv.trans
    (closedPushforwardRingHEquiv I.subschemeι _ ρ q)

include hL in
/-- Closed line vanishing forces finite original cohomology to vanish by Nakayama. -/
theorem finite_vanishing [X.IsSeparated] {R : Type} [CommRing R]
    (ρ : R →+* Γ(X, ⊤)) (a : R) (ha : a ∈ Ideal.jacobson (⊥ : Ideal R))
    (hIa : ∀ U : X.affineOpens, I.ideal U =
      Ideal.span {X.presheaf.map U.1.leTop.op (ρ a)})
    [Mono (scalarEnd (structureModule X) (ρ a))] (q : ℕ)
    [Module.Finite R (ModuleRingH ρ L q)]
    [Subsingleton (ModuleH ((Scheme.Modules.pullback I.subschemeι).obj L) q)] :
    Subsingleton (ModuleRingH ρ L q) := by
  let _ := LineScalarMonicity.scalarEnd_mono L (ρ a) hL
  let e := quotientEquiv I L hL (ρ a) hIa ρ q
  let _ : Subsingleton (ModuleH (cokernel (scalarEnd L (ρ a))) q) :=
    ⟨fun x y ↦ e.injective (Subsingleton.elim
      (α := ModuleH ((Scheme.Modules.pullback I.subschemeι).obj L) q) _ _)⟩
  exact PrincipalScalarCohomology.finite_vanishing L ρ a ha q

end FLT.Mazur.PrincipalClosedLineCohomology
