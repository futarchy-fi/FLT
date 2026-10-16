/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertBoundaryCertifiedAlgebra
public import FLT.Mazur.HilbertBoundaryFiniteLiftCover
public import FLT.Mazur.RelativeRelationSimultaneousLiftCover

/-!
# Simultaneous lifting neighborhoods on the original Hilbert boundary

Finitely many certified original boundary sections have one finite cover
by principal neighborhoods with affine original sources and lifts of every
selected section on each member. Coverage remains conditional on the actual
source certificates; the proper-family hypotheses supply Noetherianity and
compact relation domains, not those missing certificates.
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

/-- Actual common multipliers for the selected original boundary sections. -/
def originalBoundaryCommonLiftIdeal : Ideal ((invariantSheaf e).obj.obj (op W)) :=
  simultaneousSectionLiftIdeal φ v s

local notation "J" => originalBoundaryCommonLiftIdeal f hL d V c k W v s

/-- The open union supplied by actual simultaneous lifting multipliers. -/
def originalBoundaryCommonLiftOpen : TopologicalSpace.Opens (Orbit e) :=
  sectionIdealOpen (ringedSpace e) W J

local notation "N" => originalBoundaryCommonLiftOpen f hL d V c k W v s

/-- One finite identity on the closed source uses common multipliers for all selected sections. -/
theorem originalBoundary_common_source_certificate
    (hv : ∀ j ∈ s, v j ∈ originalBoundaryCertifiedSections f hL d V c k W) :
    ∃ a : J →₀ (sourceSheaf ec).obj.obj (op Wc),
      a.sum (fun b coeff ↦ coeff * (invariantInclusion ec).hom.app (op Wc)
        ((m).c.app (op W) b.val)) = 1 :=
  simultaneous_source_lift_certificate φ ιc v s hv

variable (hW : IsAffineOpen (pullOpen (equivalence f hL d V c k) W).val)
include hW

/-- Separate certificates cover the entire original boundary with common lifting neighborhoods. -/
theorem originalBoundaryCommonLiftOpen_boundary_cover
    (hv : ∀ j ∈ s, v j ∈ originalBoundaryCertifiedSections f hL d V c k W) :
    (TopologicalSpace.Opens.map (m).base).obj N = Wc :=
  simultaneousLiftOpen_boundary_cover e ec (i).left (z).left
    (originalClosedArrow_left_fst f hL d V c k)
    (originalClosedArrow_left_snd f hL d V c k) W v s
    (originalBoundaryLift_closedSource_affine f hL d V c k W hW) hv

/-- Proper-family geometry gives a finite common cover with actual lifts of every generator. -/
theorem originalBoundaryCommonLiftOpen_finite_affine_lifts :
    ∃ indices : Finset J, (N : Set (Orbit e)) =
        ⋃ a ∈ indices, (invariantPrincipal e W a.val : Set (Orbit e)) ∧
      ∀ a ∈ indices, IsAffineOpen (pullOpen e (invariantPrincipal e W a.val)).val ∧
        ∀ j ∈ s, ∃ b : (invariantSheaf e).obj.obj (op (invariantPrincipal e W a.val)),
          (m).c.app (op (invariantPrincipal e W a.val)) b =
            (invariantSheaf ec).obj.map ((TopologicalSpace.Opens.map (m).base).map
              (homOfLE (invariantPrincipal_le e W a.val))).op (v j) := by
  let _ := selectedAffineHilbertSource_isNoetherian f d V k
  exact simultaneousLiftOpen_finite_affine_lifts e ec (i).left (z).left
    (originalClosedArrow_left_fst f hL d V c k)
    (originalClosedArrow_left_snd f hL d V c k) W v s hW
    ((p).left.isCompact_preimage hW.isCompact)

end FLT.Mazur.HilbertChart.AffineRestriction
