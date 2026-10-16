/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertBoundaryCertifiedAlgebra
public import FLT.Mazur.RelativeRelationGeometricGroundSections
public import FLT.Mazur.CanonicalSchemeRelationGround
public import FLT.Mazur.AffineHilbertDerivedNoetherianRelation
public import FLT.Mazur.AffineHilbertSymmetricNeighborhoods
public import FLT.Mazur.RelativeRelationInvariantMapSections

/-!
# Actual geometric ground tests for the original Hilbert boundary

The full original and closed relations satisfy the compactness and separatedness
needed for geometric function base change. Canonical flat surjective affine tests
then detect the original invariant-sheaf boundary certificate and its finite identity.
The certificate on the geometric test still has to be constructed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve SchemeOpenEnvelope Approximation TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [IsAffine V.left] [Etale V.hom]
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

local notation "m" => originalClosedInvariantMap f hL d V c k

/-- The full closed relation is closed in the unchanged original relation. -/
instance originalClosedGroundArrow_closed : IsClosedImmersion (z).left := by
  change IsClosedImmersion (pullback.fst (p).left (i).left)
  infer_instance

/-- The complete original relation is compact on the selected affine translation chart. -/
local instance relationCompact : CompactSpace (D).left := by
  let _ := fullRelation_isNoetherian f hL d V c k
  infer_instance

/-- The closed relation is compact because its actual inclusion is closed. -/
instance originalClosedGround_compact : CompactSpace (C).left :=
  QuasiCompact.compactSpace_of_compactSpace (z).left

/-- The closed relation inherits separatedness from the actual original relation. -/
instance originalClosedGround_separated : (C).left.IsSeparated := by
  refine ⟨?_⟩
  rw [← terminal.comp_from (z).left]
  infer_instance

attribute [local irreducible] originalBoundarySource originalBoundarySourceMap
  originalClosedRelation originalClosedFst originalClosedSnd originalClosedArrow
  originalClosedEquivalence relation fst snd equivalence
attribute [local instance] SchemeFunctionGroundChange.sectionAlgebra
open SchemeFunctionGroundChange
local notation "hp" => originalClosedArrow_fst f hL d V c k
local notation "hq" => originalClosedArrow_snd f hL d V c k
local notation "φ" => SchemeRelationFunctionDiagram.invariantMap p q r s i z hp hq

omit [IsAffine V.left] in
/-- Global structural function coordinates preserve the original boundary certificate. -/
theorem originalBoundaryCertifiedSections_function_iff
    (t : (invariantSheaf ec).obj.obj (op ⊤)) :
    topFunctionEquiv ec t ∈ sourceCertifiedSections (φ).toRingHom
      (AlgHom.equalizer (sectionMap r) (sectionMap s)).val.toRingHom ↔
    t ∈ originalBoundaryCertifiedSections f hL d V c k ⊤ := by
  apply SectionLiftCertificateEquiv.certified_iff _ _ _ _
    (topFunctionEquiv e) (topFunctionEquiv ec) (RingEquiv.refl _)
  · intro a
    apply Subtype.ext
    change (i).left.appTop ((invariantInclusion e).hom.app (op ⊤) a) =
      (invariantInclusion ec).hom.app (op ⊤) ((m).c.app (op ⊤) a)
    have h := invariantMap_source_apply e ec (i).left (z).left
      (congrArg Over.Hom.left hp) (congrArg Over.Hom.left hq) ⊤ a
    change (invariantInclusion ec).hom.app (op ⊤) ((m).c.app (op ⊤) a) =
      (i).left.appLE ⊤ ⊤ _ ((invariantInclusion e).hom.app (op ⊤) a) at h
    simpa [Scheme.Hom.appLE] using h.symm
  · intro a
    rfl

variable {T : Scheme} [IsAffine T] (g : T ⟶ Spec (.of R)) [Flat g] [Surjective g]
open CanonicalSchemeRelationGround
local notation "φg" => CanonicalSchemeRelationGround.invariantMap g p q r s i z hp hq

/-- The actual original section as a function invariant on the canonical geometric test. -/
def originalBoundaryGeometricSection (t : (invariantSheaf ec).obj.obj (op ⊤)) :
    AlgHom.equalizer (sectionMap (groundMap g r)) (sectionMap (groundMap g s)) := by
  let _ := FlatGlobalFunctionBaseChange.sectionAlgebra g
  exact CanonicalSchemeRelationGround.invariantsEquiv g r s
    (1 ⊗ₜ[Γ(Spec (.of R), ⊤)] topFunctionEquiv ec t)

/-- Geometric flat surjective tests detect exactly the original sheaf certificate. -/
theorem originalBoundaryCertifiedSections_geometric_iff
    (t : (invariantSheaf ec).obj.obj (op ⊤)) :
    originalBoundaryGeometricSection f hL d V c k g t ∈ sourceCertifiedSections
      (φg).toRingHom (AlgHom.equalizer (sectionMap (groundMap g r))
        (sectionMap (groundMap g s))).val.toRingHom ↔
    t ∈ originalBoundaryCertifiedSections f hL d V c k ⊤ :=
  (CanonicalSchemeRelationGround.certified_iff g p q r s i z hp hq
    (topFunctionEquiv ec t)).trans
      (originalBoundaryCertifiedSections_function_iff f hL d V c k t)

/-- A geometric relation certificate gives a finite identity on the original source. -/
theorem originalBoundary_certificate_of_geometric_test
    (t : (invariantSheaf ec).obj.obj (op ⊤))
    (ht : originalBoundaryGeometricSection f hL d V c k g t ∈ sourceCertifiedSections
      (φg).toRingHom (AlgHom.equalizer (sectionMap (groundMap g r))
        (sectionMap (groundMap g s))).val.toRingHom) :
    ∃ a : originalBoundaryLiftIdeal f hL d V c k ⊤ t →₀
        (sourceSheaf ec).obj.obj (op ⊤),
      a.sum (fun v b ↦ b * (invariantInclusion ec).hom.app (op ⊤)
        ((m).c.app (op ⊤) v.val)) = 1 :=
  (mem_originalBoundaryCertifiedSections_iff f hL d V c k ⊤ t).mp
    ((originalBoundaryCertifiedSections_geometric_iff f hL d V c k g t).mp ht)

/-- The geometric test certificate covers the actual unchanged original closed boundary. -/
theorem originalBoundary_cover_of_geometric_test
    (t : (invariantSheaf ec).obj.obj (op ⊤))
    (ht : originalBoundaryGeometricSection f hL d V c k g t ∈ sourceCertifiedSections
      (φg).toRingHom (AlgHom.equalizer (sectionMap (groundMap g r))
        (sectionMap (groundMap g s))).val.toRingHom) :
    (TopologicalSpace.Opens.map (m).base).obj
      (originalBoundaryLiftOpen f hL d V c k ⊤ t) = ⊤ :=
  (mem_originalBoundaryCertifiedSections_iff_cover f hL d V c k ⊤ t
    (originalClosed_top_affine f hL d V c k)).mp
      ((originalBoundaryCertifiedSections_geometric_iff f hL d V c k g t).mp ht)

end FLT.Mazur.HilbertChart.AffineRestriction
