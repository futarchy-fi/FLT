/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCubicFiniteFamily
public import FLT.Mazur.ModuleSectionRatioOpen

/-!
# Nonvanishing opens of the finite polygon cubic family

Every chosen denominator has its actual generator open. The retained pair
proves these opens cover the polygon. Ratios are regular functions on these
opens, with restriction and change-of-denominator identities on intersections.
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

/-- The actual nonvanishing open of each cubic denominator. -/
def cubicOpen (i : CubicIndex.{u} n) : C.left.Opens :=
  sectionGeneratorOpen (polygonLine K n hn p q h a 3) (cubicFamily K n hn p q h a i)

/-- The denominator generates on its own open. -/
instance cubicOpen_sectionHom_isIso (i : CubicIndex.{u} n) :
    IsIso (sectionHom (polygonLine K n hn p q h a 3) (cubicOpen K n hn p q h a i)
      ((polygonLine K n hn p q h a 3).presheaf.map (homOfLE le_top).op
        (cubicFamily K n hn p q h a i))) :=
  sectionHom_generatorOpen_isIso _ _

/-- The actual nonvanishing opens cover every point of the polygon. -/
theorem iSup_cubicOpen : ⨆ i, cubicOpen K n hn p q h a i = ⊤ := by
  apply top_unique
  intro x _
  by_cases hx : x ∈ (PolygonBoundaryDivisor.ideal K n p a).support
  · obtain ⟨i, hi⟩ := support_mem_torusOpen K n hn p q h a x hx
    have := interiorSection_isIso_torusOpen K n hn p q h a i
    have hle := le_sectionGeneratorOpen (polygonLine K n hn p q h a 3)
      (nodeSection K n hn p q h a 0 1 0) (torusOpen K n hn p q h i)
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨.inl ⟨true⟩, hle hi⟩
  · have hs := canonicalSection_isIso_complement K n hn p q h a
    have hsec : IsIso (sectionHom (polygonLine K n hn p q h a 3)
        (divisorComplement K n p a)
        ((polygonLine K n hn p q h a 3).presheaf.map (homOfLE le_top).op
          (generatingPair K n hn p q h a ⟨false⟩))) := by
      change IsIso (sectionHom _ (divisorComplement K n p a)
        ((polygonLine K n hn p q h a 3).presheaf.map (homOfLE le_top).op
          (divisorSection ((PolygonBoundaryDivisor.cartier K n p hn q h a).1.pow 3) ⊤)))
      rw [divisorSection_restrict]
      exact hs
    have hle := le_sectionGeneratorOpen (polygonLine K n hn p q h a 3)
      (generatingPair K n hn p q h a ⟨false⟩) (divisorComplement K n p a)
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨.inl ⟨false⟩, hle hx⟩

/-- A cubic coordinate ratio on any subopen of its denominator open. -/
def cubicRatioOn (i j : CubicIndex.{u} n) (U : C.left.Opens)
    (hi : U ≤ cubicOpen K n hn p q h a i) : Γ(C.left, U) :=
  sectionRatioOn (polygonLine K n hn p q h a 3) (cubicFamily K n hn p q h a i)
    U hi (cubicFamily K n hn p q h a j)

/-- Cubic ratios commute with restriction to common opens. -/
lemma cubicRatioOn_restrict (i j : CubicIndex.{u} n) (U V : C.left.Opens)
    (hi : U ≤ cubicOpen K n hn p q h a i) (hVU : V ≤ U) :
    C.left.presheaf.map (homOfLE hVU).op (cubicRatioOn K n hn p q h a i j U hi) =
      cubicRatioOn K n hn p q h a i j V (hVU.trans hi) :=
  sectionRatioOn_restrict _ _ U V hi hVU _

/-- Transition ratios satisfy the multiplicative identity on every common open. -/
lemma cubicRatioOn_change (i j k : CubicIndex.{u} n) (U : C.left.Opens)
    (hi : U ≤ cubicOpen K n hn p q h a i) (hj : U ≤ cubicOpen K n hn p q h a j) :
    cubicRatioOn K n hn p q h a i j U hi * cubicRatioOn K n hn p q h a j k U hj =
      cubicRatioOn K n hn p q h a i k U hi :=
  sectionRatioOn_change _ _ _ _ U hi hj

end FLT.Mazur.PolygonCubicSections
