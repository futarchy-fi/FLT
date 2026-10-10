/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperLinePushforwardLocalFree

/-!
# Rank loci of acyclic proper line direct images

The rank is computed on the actual module of sections. Residue-fiber
vanishing makes every fixed-rank locus clopen, and the canonical section
comparison identifies its inverse image after every affine base change.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open Scheme.Modules
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.LineSectionBaseChange
open FCurve Chow IncreasingCechCoefficients IncreasingCechScalars

variable {X S : Scheme.{0}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  (f : X ⟶ S) [IsProper f] [Flat f] (L : X.Modules) (hL : LocallyFreeRankOne L)
  (hV : ∀ (z : PrimeSpectrum Γ(S, ⊤)) n,
    Subsingleton (ModuleH (residueAlgebraFiberLine f L z) (n + 1)))

include hL hV in
/-- The actual section rank varies locally constantly on the affine base. -/
theorem properLineSectionRank_locallyConstant :
    IsLocallyConstant (Module.rankAtStalk (R := Γ(S, ⊤)) (baseSections L f.appTop.hom ⊤)) := by
  let _ := hL.isFinitePresentation
  let _ := proper_sections_finite f L
  let _ := projective_sections_of_residue_fibers f L hL hV
  let _ := Module.finitePresentation_of_projective Γ(S, ⊤)
    (baseSections L f.appTop.hom ⊤)
  exact Module.isLocallyConstant_rankAtStalk

/-- The open parameter locus where the actual proper direct image has specified rank. -/
def properLineSectionRankOpen (d : ℕ) : Opens (PrimeSpectrum Γ(S, ⊤)) :=
  ⟨{z | Module.rankAtStalk (R := Γ(S, ⊤)) (baseSections L f.appTop.hom ⊤) z = d},
    (properLineSectionRank_locallyConstant f L hL hV).isOpen_fiber d⟩

/-- Membership uses the actual original section module. -/
lemma mem_properLineSectionRankOpen (d : ℕ) (z : PrimeSpectrum Γ(S, ⊤)) :
    z ∈ properLineSectionRankOpen f L hL hV d ↔
      Module.rankAtStalk (R := Γ(S, ⊤)) (baseSections L f.appTop.hom ⊤) z = d := Iff.rfl

/-- On the acyclic family each fixed-rank locus is also closed. -/
lemma properLineSectionRankOpen_isClosed (d : ℕ) :
    IsClosed (properLineSectionRankOpen f L hL hV d : Set (PrimeSpectrum Γ(S, ⊤))) :=
  (properLineSectionRank_locallyConstant f L hL hV).isClosed_fiber d

variable {P T : Scheme.{0}} [IsAffine T]
  {p : P ⟶ X} {q : P ⟶ T} {g : T ⟶ S} (h : IsPullback p q f g)

include h hL hV in
/-- The original section rank commutes with arbitrary affine base change. -/
theorem properLineSectionRank_baseChange (z : PrimeSpectrum Γ(T, ⊤)) :
    Module.rankAtStalk (R := Γ(T, ⊤)) (baseSections ((pullback p).obj L) q.appTop.hom ⊤) z =
      Module.rankAtStalk (R := Γ(S, ⊤)) (baseSections L f.appTop.hom ⊤)
        (PrimeSpectrum.comap g.appTop.hom z) := by
  let _ := hL.isFinitePresentation
  let _ := proper_sections_finite f L
  let _ := projective_sections_of_residue_fibers f L hL hV
  let _ : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
  let e := LinearEquiv.ofBijective (globalComparison h L)
    (canonical_bijective_of_residue_fibers f L hL hV h)
  rw [← Module.rankAtStalk_eq_of_equiv e]
  exact Module.rankAtStalk_baseChange z

include h hL hV in
/-- Every new affine base has precisely the inverse-image rank locus, without Noetherianity. -/
theorem properLineSectionRank_preimage (d : ℕ) :
    {z | Module.rankAtStalk (R := Γ(T, ⊤))
      (baseSections ((pullback p).obj L) q.appTop.hom ⊤) z = d} =
      PrimeSpectrum.comap g.appTop.hom ⁻¹'
        (properLineSectionRankOpen f L hL hV d : Set (PrimeSpectrum Γ(S, ⊤))) := by
  ext z
  exact congrArg (· = d) (properLineSectionRank_baseChange f L hL hV h z) |>.to_iff

include h hL hV in
/-- The rank condition stays open and closed after an arbitrary affine base change. -/
theorem properLineSectionRank_baseChange_isClopen (d : ℕ) :
    IsClopen {z | Module.rankAtStalk (R := Γ(T, ⊤))
      (baseSections ((pullback p).obj L) q.appTop.hom ⊤) z = d} := by
  rw [properLineSectionRank_preimage f L hL hV h d]
  exact ⟨(properLineSectionRankOpen_isClosed f L hL hV d).preimage
    (PrimeSpectrum.continuous_comap g.appTop.hom),
    (properLineSectionRankOpen f L hL hV d).isOpen.preimage
      (PrimeSpectrum.continuous_comap g.appTop.hom)⟩

end FLT.Mazur.LineSectionBaseChange
