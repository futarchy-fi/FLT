/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertBoundaryFlatCertificate
public import FLT.Mazur.HilbertBoundarySimultaneousLiftCover

/-!
# Common original neighborhoods from independent faithfully flat tests

Each of finitely many boundary sections may be certified on its own faithfully
flat scalar test. Descent returns all certificates to the unchanged original
source. Their common multipliers give one finite affine-source lifting cover.
The separate tests need no comparison maps or common chosen ground.
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

variable {ι : Type*}
  (v : ι → (invariantSheaf (originalClosedEquivalence f hL d V c k)).obj.obj
    (op ((TopologicalSpace.Opens.map
      (originalClosedInvariantMap f hL d V c k).base).obj W))) (s : Finset ι)

variable (S : ι → Type*) [∀ j, CommRing (S j)]
  [∀ j, Algebra ((invariantSheaf (equivalence f hL d V c k)).obj.obj (op W)) (S j)]
  [∀ j, Module.FaithfullyFlat
    ((invariantSheaf (equivalence f hL d V c k)).obj.obj (op W)) (S j)]

local notation "J" => originalBoundaryCommonLiftIdeal f hL d V c k W v s
local notation "N" => originalBoundaryCommonLiftOpen f hL d V c k W v s

/-- Independent flat tests construct one original finite certificate with common multipliers. -/
theorem originalBoundary_common_certificate_of_flat_tests
    (hv : ∀ j ∈ s, SectionLiftBaseChange.boundarySection φ (S j) (v j) ∈
    sourceCertifiedSections (SectionLiftBaseChange.restriction φ (S j))
      (SectionLiftBaseChange.testMap φ ιc (S j))) :
    ∃ a : J →₀ (sourceSheaf ec).obj.obj (op Wc),
      a.sum (fun b coeff ↦ coeff * (invariantInclusion ec).hom.app (op Wc)
        ((m).c.app (op W) b.val)) = 1 := by
  apply originalBoundary_common_source_certificate f hL d V c k W v s
  intro j hj
  exact (originalBoundaryCertifiedSections_baseChange_iff f hL d V c k W
    (S j) (v j)).mp (hv j hj)

variable (hW : IsAffineOpen (pullOpen (equivalence f hL d V c k) W).val)
include hW

/-- Descended common multipliers cover every original boundary point of the domain. -/
theorem originalBoundary_common_cover_of_flat_tests
    (hv : ∀ j ∈ s, SectionLiftBaseChange.boundarySection φ (S j) (v j) ∈
    sourceCertifiedSections (SectionLiftBaseChange.restriction φ (S j))
      (SectionLiftBaseChange.testMap φ ιc (S j))) :
    (TopologicalSpace.Opens.map (m).base).obj N = Wc := by
  apply originalBoundaryCommonLiftOpen_boundary_cover f hL d V c k W v s hW
  intro j hj
  exact (originalBoundaryCertifiedSections_baseChange_iff f hL d V c k W
    (S j) (v j)).mp (hv j hj)

/-- The independent tests give one finite original cover carrying actual lifts of all sections. -/
theorem originalBoundary_finite_common_lifts_of_flat_tests
    (hv : ∀ j ∈ s, SectionLiftBaseChange.boundarySection φ (S j) (v j) ∈
    sourceCertifiedSections (SectionLiftBaseChange.restriction φ (S j))
      (SectionLiftBaseChange.testMap φ ιc (S j))) :
    (TopologicalSpace.Opens.map (m).base).obj N = Wc ∧
      ∃ indices : Finset J, (N : Set (Orbit e)) =
        ⋃ a ∈ indices, (invariantPrincipal e W a.val : Set (Orbit e)) ∧
        ∀ a ∈ indices, IsAffineOpen (pullOpen e (invariantPrincipal e W a.val)).val ∧
          ∀ j ∈ s, ∃ b : (invariantSheaf e).obj.obj (op (invariantPrincipal e W a.val)),
            (m).c.app (op (invariantPrincipal e W a.val)) b =
              (invariantSheaf ec).obj.map ((TopologicalSpace.Opens.map (m).base).map
                (homOfLE (invariantPrincipal_le e W a.val))).op (v j) :=
  ⟨originalBoundary_common_cover_of_flat_tests f hL d V c k W v s S hW hv,
    originalBoundaryCommonLiftOpen_finite_affine_lifts f hL d V c k W v s hW⟩

end FLT.Mazur.HilbertChart.AffineRestriction
