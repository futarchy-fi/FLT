/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RegularPrincipalStructureQuotient
public import FLT.Mazur.PrincipalScalarCohomology
public import FLT.Mazur.ClosedPushforwardCohomology
public import FLT.Mazur.PowerSeriesParameterFlatness

/-!
# Actual cohomology across a principal closed fiber

The principal scalar cokernel computes cohomology on the actual closed
subscheme. Constants lifting to the total space give parameter regularity
on its original first cohomology.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.PrincipalClosedCohomology

open FCurve IdealPowerScalarLift RegularPrincipalStructureQuotient

universe u

set_option backward.isDefEq.respectTransparency false

variable {X : Scheme.{u}} [X.IsSeparated] [IsLocallyNoetherian X]
  (I : X.IdealSheafData) (r : Γ(X, ⊤))
  (hI : ∀ U : X.affineOpens, I.ideal U =
    Ideal.span {X.presheaf.map U.1.leTop.op r})
  [Mono (scalarEnd (structureModule X) r)]

/-- Scalar-quotient cohomology is actual closed-subscheme cohomology over the original base. -/
def quotientEquiv {R : Type u} [CommRing R] (ρ : R →+* Γ(X, ⊤)) (q : ℕ) :
    ModuleRingH ρ (cokernel (scalarEnd (structureModule X) r)) q ≃ₗ[R]
      ModuleRingH (I.subschemeι.appTop.hom.comp ρ) (structureModule I.subscheme) q := by
  let _ := LocallyOfFiniteType.isLocallyNoetherian I.subschemeι
  let _ := CoherentIdealIntersection.structureModule_coherent (X := I.subscheme)
  exact ((moduleRingHFunctor ρ q).mapIso (structureCokernelIso I r hI)).toLinearEquiv.trans
    (closedPushforwardRingHEquiv I.subschemeι (structureModule I.subscheme) ρ q)

include hI in
/-- Vanishing on the actual closed subscheme gives vanishing of the scalar cokernel. -/
theorem quotient_subsingleton (q : ℕ)
    [Subsingleton (ModuleH (structureModule I.subscheme) q)] :
    Subsingleton (ModuleH (cokernel (scalarEnd (structureModule X) r)) q) := by
  let e := quotientEquiv I r hI (RingHom.id Γ(X, ⊤)) q
  constructor
  intro x y
  apply e.injective
  exact Subsingleton.elim (α := ModuleH (structureModule I.subscheme) q) _ _

omit [X.IsSeparated] in
include hI in
/-- Lifting actual closed functions makes actual scalar-quotient H0 restriction surjective. -/
theorem quotient_h0_surjective (h0 : Function.Surjective I.subschemeι.appTop) :
    Function.Surjective (moduleHMap (cokernel.π (scalarEnd (structureModule X) r)) 0) := by
  let e := structureCokernelIso I r hI
  have hs : Function.Surjective ((cokernel.π (scalarEnd (structureModule X) r)).app ⊤) := by
    intro s
    obtain ⟨t, ht⟩ := h0 (e.hom.app ⊤ s)
    refine ⟨t, ModuleSubobjectCoverEquality.app_injective e.hom ⊤ ?_⟩
    have he := congr($(structureCokernelIso_projection I r hI).app ⊤ t)
    exact he.trans ht
  intro x
  obtain ⟨s, hs⟩ := hs (moduleH0Equiv _ x)
  refine ⟨(moduleH0Equiv _).symm s, (moduleH0Equiv _).injective ?_⟩
  rw [moduleH0Equiv_naturality, LinearEquiv.apply_symm_apply]
  exact hs

omit [X.IsSeparated] in
include hI in
/-- Closed constants lifting makes the original first cohomology parameter-torsion-free. -/
theorem h1_regular (h0 : Function.Surjective I.subschemeι.appTop)
    (x : ModuleH (structureModule X) 1) (hx : r • x = 0) : x = 0 :=
  PrincipalScalarCohomology.scalar_regular (structureModule X) r 0
    (quotient_h0_surjective I r hI h0) x hx

/-- Finite original cohomology vanishes when its actual principal closed fiber does. -/
theorem finite_vanishing {R : Type u} [CommRing R] (ρ : R →+* Γ(X, ⊤))
    (a : R) (ha : a ∈ Ideal.jacobson (⊥ : Ideal R))
    (hIa : ∀ U : X.affineOpens, I.ideal U =
      Ideal.span {X.presheaf.map U.1.leTop.op (ρ a)})
    [Mono (scalarEnd (structureModule X) (ρ a))] (q : ℕ)
    [Module.Finite R (ModuleRingH ρ (structureModule X) q)]
    [Subsingleton (ModuleH (structureModule I.subscheme) q)] :
    Subsingleton (ModuleRingH ρ (structureModule X) q) := by
  let _ := quotient_subsingleton I (ρ a) hIa q
  exact PrincipalScalarCohomology.finite_vanishing (structureModule X) ρ a ha q

end FLT.Mazur.PrincipalClosedCohomology
