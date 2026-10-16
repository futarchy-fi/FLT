/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertBoundaryLiftLocus
public import FLT.Mazur.RelativeRelationFiniteLiftCover
public import FLT.Mazur.RelativeRelationIdealCertificate

/-!
# Finite original boundary lifting covers from proper-family geometry

The original proper family and its selected affine Hilbert source give a
Noetherian orbit topology. Consequently the actual principal lifting locus
has a finite cover by actual principal neighborhoods with affine source
inverse images and actual lifts of the original boundary section.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
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

/-- The unchanged original orbit topology is Noetherian for every etale translation. -/
theorem originalOrbit_noetherianSpace : NoetherianSpace (Orbit e) := by
  let _ := selectedAffineHilbertSource_isNoetherian f d V k
  exact orbit_noetherianSpace e

variable (W : TopologicalSpace.Opens (Orbit (equivalence f hL d V c k)))
  (t : (invariantSheaf (originalClosedEquivalence f hL d V c k)).obj.obj
    (op ((TopologicalSpace.Opens.map
      (originalClosedInvariantMap f hL d V c k).base).obj W)))
  (hW : IsAffineOpen (pullOpen (equivalence f hL d V c k) W).val)
local notation "J" => originalBoundaryLiftIdeal f hL d V c k W t
local notation "N" => originalBoundaryLiftOpen f hL d V c k W t

include hW in
/-- The actual original lifting locus has a finite cover with affine sources and boundary lifts. -/
theorem originalBoundaryLiftOpen_finite_affine_lifts :
    ∃ indices : Finset J, (N : Set (Orbit e)) =
        ⋃ a ∈ indices, (invariantPrincipal e W a.val : Set (Orbit e)) ∧
      ∀ a ∈ indices, IsAffineOpen (pullOpen e (invariantPrincipal e W a.val)).val ∧
        ∃ b : (invariantSheaf e).obj.obj (op (invariantPrincipal e W a.val)),
          (m).c.app (op (invariantPrincipal e W a.val)) b =
            (invariantSheaf ec).obj.map ((TopologicalSpace.Opens.map (m).base).map
              (homOfLE (invariantPrincipal_le e W a.val))).op t := by
  let _ := selectedAffineHilbertSource_isNoetherian f d V k
  exact principalLiftOpen_finite_affine_lifts e ec (i).left (z).left
    (originalClosedArrow_left_fst f hL d V c k)
    (originalClosedArrow_left_snd f hL d V c k) W t hW
    ((p).left.isCompact_preimage hW.isCompact)

include hW in
/-- Covering the original domain amounts to a finite coefficient identity on its affine source. -/
theorem originalBoundaryLiftOpen_eq_iff_certificate :
    N = W ↔ ∃ a : J →₀ (sourceSheaf e).obj.obj (op W),
      a.sum (fun v b ↦ b * (invariantInclusion e).hom.app (op W) v.val) = 1 :=
  sectionIdealOpen_eq_iff_sourceCertificate e W J hW

end FLT.Mazur.HilbertChart.AffineRestriction
