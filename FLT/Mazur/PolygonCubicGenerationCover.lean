/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DivisorSectionComplement
public import FLT.Mazur.PolygonCubicSections

/-!
# The divisor-complement and torus cover of the polygon

The canonical cubic section generates on the complement of the marked divisor.
Together with the actual open torus charts this open covers the polygon,
including self-incidence and both nodes of a two-gon.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.PolygonCubicSections
open FCurve PolygonPinching PolygonPowerNodeEndpoints
variable (K : Type u) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
  (a : Fin n → Kˣ)

/-- The marked-divisor complement, on which the canonical section generates. -/
def divisorComplement : C.left.Opens := (PolygonBoundaryDivisor.ideal K n p a).support.compl

/-- The actual cubic section map is invertible on the divisor complement. -/
theorem canonicalSection_isIso_complement :
    IsIso (sectionHom (polygonLine K n hn p q h a 3) (divisorComplement K n p a)
      (divisorSection ((PolygonBoundaryDivisor.cartier K n p hn q h a).1.pow 3)
        (divisorComplement K n p a))) := by
  apply divisorSection_isIso_off_support
  intro x hx
  change x ∉ (PolygonBoundaryDivisor.ideal K n p a).support at hx
  simpa only [Scheme.IdealSheafData.support_pow_succ] using hx

/-- The open image of the specified torus chart. -/
def torusOpen (i : Fin n) : C.left.Opens := by
  let := torus_isOpenImmersion K n hn p q h i
  exact (torusToComponent K ≫ componentι K n i ≫ p).left.opensRange

/-- The actual torus opens cover every marked-divisor point. -/
lemma support_mem_torusOpen (x : C.left)
    (hx : x ∈ (PolygonBoundaryDivisor.ideal K n p a).support) :
    ∃ i, x ∈ torusOpen K n hn p q h i := by
  obtain ⟨i, y, rfl⟩ := (PolygonBoundaryDivisor.mem_support_iff K n p hn q h a x).mp hx
  exact ⟨i, PolygonMarkedSections.section_mem_torus K n p (a i) i y⟩

/-- The divisor complement and torus charts form an open cover. -/
theorem complement_sup_torus :
    divisorComplement K n p a ⊔ ⨆ i, torusOpen K n hn p q h i = ⊤ := by
  apply top_unique
  intro x _
  by_cases hx : x ∈ (PolygonBoundaryDivisor.ideal K n p a).support
  · obtain ⟨i, hi⟩ := support_mem_torusOpen K n hn p q h a x hx
    exact Or.inr (TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hi⟩)
  · exact Or.inl hx

end FLT.Mazur.PolygonCubicSections
