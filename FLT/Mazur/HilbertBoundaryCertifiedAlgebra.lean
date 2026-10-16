/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertBoundaryLocalCoverCriterion
public import FLT.Mazur.SectionLiftCertificatePolynomial

/-!
# Algebraic generation of original boundary lifting certificates

The actual original boundary sections with finite source certificates form a
subring. Certificates for generators give certificates for their polynomials
and unit inverses. The remaining geometric obligation is to certify enough
generators; no such generation or coverage hypothesis is built into the ring.
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

/-- The subring defined by actual lifting certificates on the original closed source. -/
def originalBoundaryCertifiedSections : Subring ((invariantSheaf ec).obj.obj (op Wc)) :=
  sourceCertifiedSections φ ιc

/-- The abstract source ideal is exactly the already defined original closed-source ideal. -/
theorem originalBoundaryLiftClosedSourceIdeal_eq
    (t : (invariantSheaf ec).obj.obj (op Wc)) :
    originalBoundaryLiftClosedSourceIdeal f hL d V c k W t =
      sectionLiftSourceIdeal φ ιc t := rfl

/-- Membership is the actual finite identity on the original boundary source. -/
theorem mem_originalBoundaryCertifiedSections_iff
    (t : (invariantSheaf ec).obj.obj (op Wc)) :
    t ∈ originalBoundaryCertifiedSections f hL d V c k W ↔
      ∃ a : originalBoundaryLiftIdeal f hL d V c k W t →₀
          (sourceSheaf ec).obj.obj (op Wc),
        a.sum (fun v b ↦ b * (invariantInclusion ec).hom.app (op Wc)
          ((m).c.app (op W) v.val)) = 1 :=
  mem_sourceCertifiedSections_iff φ ιc t

/-- For affine original source domains, this subring is exactly the boundary-covered sections. -/
theorem mem_originalBoundaryCertifiedSections_iff_cover
    (t : (invariantSheaf ec).obj.obj (op Wc))
    (hW : IsAffineOpen (pullOpen e W).val) :
    t ∈ originalBoundaryCertifiedSections f hL d V c k W ↔
      (TopologicalSpace.Opens.map (m).base).obj
        (originalBoundaryLiftOpen f hL d V c k W t) = Wc := by
  rw [originalBoundaryLift_boundary_cover_iff f hL d V c k W t hW,
    originalBoundaryLiftClosedSourceIdeal_eq]
  rfl

/-- Original invariant functions supply actual certificates without a geometric hypothesis. -/
theorem originalBoundaryCertifiedSections_image
    (a : (invariantSheaf e).obj.obj (op W)) :
    φ a ∈ originalBoundaryCertifiedSections f hL d V c k W :=
  image_mem_sourceCertifiedSections φ ιc a

/-- Polynomial combinations of certified boundary generators have actual finite certificates. -/
theorem originalBoundaryCertifiedSections_polynomial {ι : Type*}
    (v : ι → (invariantSheaf ec).obj.obj (op Wc))
    (hv : ∀ j, v j ∈ originalBoundaryCertifiedSections f hL d V c k W)
    (P : MvPolynomial ι ((invariantSheaf e).obj.obj (op W))) :
    MvPolynomial.eval₂ φ v P ∈ originalBoundaryCertifiedSections f hL d V c k W :=
  polynomial_mem_sourceCertifiedSections φ ιc v hv P

/-- Inverting a certified boundary unit constructs another original source certificate. -/
theorem originalBoundaryCertifiedSections_inverse
    (t u : (invariantSheaf ec).obj.obj (op Wc)) (htu : t * u = 1)
    (ht : t ∈ originalBoundaryCertifiedSections f hL d V c k W) :
    u ∈ originalBoundaryCertifiedSections f hL d V c k W :=
  inverse_mem_sourceCertifiedSections φ ιc htu ht

end FLT.Mazur.HilbertChart.AffineRestriction
