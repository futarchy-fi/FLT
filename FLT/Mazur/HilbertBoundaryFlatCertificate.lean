/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertBoundaryCertifiedAlgebra
public import FLT.Mazur.SectionLiftBaseChange

/-!
# Faithfully flat tests of original Hilbert boundary lifting certificates

Use the actual original boundary restriction and source inclusion to construct
both tensor rings. A certificate on a faithfully flat test of the original
invariant scalars descends to an actual original finite coefficient identity.
For affine source domains this proves boundary coverage, conditional only on
the tested certificate. Proper-family geometry must still supply that input.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve SchemeOpenEnvelope
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
local notation "π" => Over.Hom.left (prod.fst : prod A V ⟶ A)
local notation "O" => Scheme.Hom.opensRange (Over.Hom.left (toEnvelope f hL d V c k))
local notation "B" => originalBoundarySource f hL d V c k
local notation "i" => originalBoundarySourceMap f hL d V c k
local notation "D" => relation f hL d V c k
local notation "p" => fst f hL d V c k
local notation "q" => snd f hL d V c k

local notation "C" => originalClosedRelation f hL d V c k
local notation "r" => originalClosedFst f hL d V c k
local notation "s" => originalClosedSnd f hL d V c k
local notation "z" => originalClosedArrow f hL d V c k

open RelativeRelationOrbit
local notation "e" => equivalence f hL d V c k
local notation "ec" => originalClosedEquivalence f hL d V c k

attribute [local irreducible] originalBoundarySource originalBoundarySourceMap
  originalClosedRelation originalClosedFst originalClosedSnd originalClosedArrow
  originalClosedEquivalence relation fst snd equivalence

local notation "m" => originalClosedInvariantMap f hL d V c k

variable (W : TopologicalSpace.Opens (Orbit (equivalence f hL d V c k)))
local notation "Wc" =>
  (Functor.obj
    (TopologicalSpace.Opens.map (PresheafedSpace.Hom.base (LocallyRingedSpace.Hom.toHom m))) W)
local notation "φ" => originalClosedSectionPullback f hL d V c k W
set_option quotPrecheck false in
local notation "ιc" =>
  CommRingCat.Hom.hom ((invariantInclusion ec).hom.app (op Wc))

variable (S : Type*) [CommRing S]
  [Algebra ((invariantSheaf (equivalence f hL d V c k)).obj.obj (op W)) S]
  [Module.FaithfullyFlat ((invariantSheaf (equivalence f hL d V c k)).obj.obj (op W)) S]

/-- Faithful flat tests detect membership in the actual original certified subring. -/
theorem originalBoundaryCertifiedSections_baseChange_iff
    (t : (invariantSheaf ec).obj.obj (op Wc)) :
    SectionLiftBaseChange.boundarySection φ S t ∈
      sourceCertifiedSections (SectionLiftBaseChange.restriction φ S)
        (SectionLiftBaseChange.testMap φ ιc S) ↔
      t ∈ originalBoundaryCertifiedSections f hL d V c k W :=
  SectionLiftBaseChange.certified_iff φ ιc S t

/-- New multipliers and coefficients on a flat test construct an original finite identity. -/
theorem originalBoundary_certificate_of_baseChange
    (t : (invariantSheaf ec).obj.obj (op Wc))
    (h : SectionLiftBaseChange.boundarySection φ S t ∈
      sourceCertifiedSections (SectionLiftBaseChange.restriction φ S)
        (SectionLiftBaseChange.testMap φ ιc S)) :
    ∃ a : originalBoundaryLiftIdeal f hL d V c k W t →₀
        (sourceSheaf ec).obj.obj (op Wc),
      a.sum (fun v b ↦ b * (invariantInclusion ec).hom.app (op Wc)
        ((m).c.app (op W) v.val)) = 1 :=
  (mem_originalBoundaryCertifiedSections_iff f hL d V c k W t).mp
    ((originalBoundaryCertifiedSections_baseChange_iff f hL d V c k W S t).mp h)

/-- The descended certificate covers the unchanged original boundary, not just the new test. -/
theorem originalBoundary_cover_of_baseChange
    (t : (invariantSheaf ec).obj.obj (op Wc))
    (hW : IsAffineOpen (pullOpen e W).val)
    (h : SectionLiftBaseChange.boundarySection φ S t ∈
      sourceCertifiedSections (SectionLiftBaseChange.restriction φ S)
        (SectionLiftBaseChange.testMap φ ιc S)) :
    (TopologicalSpace.Opens.map (m).base).obj
      (originalBoundaryLiftOpen f hL d V c k W t) = Wc :=
  (mem_originalBoundaryCertifiedSections_iff_cover f hL d V c k W t hW).mp
    ((originalBoundaryCertifiedSections_baseChange_iff f hL d V c k W S t).mp h)

/-- A genuine extended invariant lift descends without selecting compatible tensor coefficients. -/
theorem originalBoundary_lift_of_baseChange
    (t : (invariantSheaf ec).obj.obj (op Wc)) (aS : S)
    (hs : SectionLiftBaseChange.restriction φ S aS =
      SectionLiftBaseChange.boundarySection φ S t) :
    ∃ a : (invariantSheaf e).obj.obj (op W), (m).c.app (op W) a = t :=
  SectionLiftBaseChange.lift_descends φ S t aS hs

end FLT.Mazur.HilbertChart.AffineRestriction
