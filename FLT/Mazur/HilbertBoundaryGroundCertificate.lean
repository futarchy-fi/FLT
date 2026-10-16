/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertBoundaryCertifiedAlgebra
public import FLT.Mazur.RelativeRelationTopCoefficientCoordinates
public import FLT.Mazur.GroundFlatEqualizerCertificate

/-!
# Full original Hilbert boundary equations under faithful ground change

The actual geometric endpoint squares construct the restriction between full
coefficient equalizers. Its flat comparison is natural, and certificates there
descend to the actual original invariant-sheaf boundary certificate on the top
source domain. Geometry must still produce a certificate on such a test.
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

/-- Source sections use the original structural coefficient map. -/
local instance sourceAlgebra : Algebra R Γ(A.left, ⊤) := affineBaseSectionAlgebra A.hom
/-- Relation sections retain the full original relation structural map. -/
local instance relationAlgebra : Algebra R Γ((D).left, ⊤) :=
  affineBaseSectionAlgebra (D).hom
/-- Boundary source sections use the original closed structural map. -/
local instance closedSourceAlgebra : Algebra R Γ((B).left, ⊤) :=
  affineBaseSectionAlgebra (B).hom
/-- Boundary relation sections retain their independent whole structural map. -/
local instance closedRelationAlgebra : Algebra R Γ((C).left, ⊤) :=
  affineBaseSectionAlgebra (C).hom

open SchemeRelationCoefficientDiagram in
/-- The original boundary map of invariant coefficient algebras. -/
def originalClosedCoefficientMap : invariants p q →ₐ[R] invariants r s :=
  invariantMap p q r s i z (originalClosedArrow_fst f hL d V c k)
    (originalClosedArrow_snd f hL d V c k)

variable (T : Type) [CommRing T] [Algebra R T] [Module.FaithfullyFlat R T]

open SchemeRelationCoefficientDiagram in
/-- Full boundary restriction after extending the original coefficient ground. -/
def originalClosedGroundMap : tensorInvariants p q T →ₐ[T] tensorInvariants r s T :=
  tensorInvariantMap p q r s i z (originalClosedArrow_fst f hL d V c k)
    (originalClosedArrow_snd f hL d V c k) T

/-- The prescribed original boundary section in the full new endpoint equalizer. -/
def originalClosedGroundSection (t : (invariantSheaf ec).obj.obj (op ⊤)) :
    SchemeRelationCoefficientDiagram.tensorInvariants r s T :=
  SchemeRelationCoefficientDiagram.flatComparison r s T
    (1 ⊗ₜ[R] topCoefficientEquiv ec t)

/-- The test uses the full original boundary source tensor as its coefficient ring. -/
def originalClosedGroundInclusion :
    SchemeRelationCoefficientDiagram.tensorInvariants r s T →+* T ⊗[R] Γ((B).left, ⊤) :=
  (SchemeRelationCoefficientDiagram.tensorInvariants r s T).val.toRingHom

/-- Whole new relation equations detect the actual original boundary certificate. -/
theorem originalBoundaryCertifiedSections_ground_iff
    (t : (invariantSheaf ec).obj.obj (op ⊤)) :
    originalClosedGroundSection f hL d V c k T t ∈ sourceCertifiedSections
      (originalClosedGroundMap f hL d V c k T).toRingHom
      (originalClosedGroundInclusion f hL d V c k T) ↔
    t ∈ originalBoundaryCertifiedSections f hL d V c k ⊤ := by
  apply Iff.trans (GroundFlatEqualizerCertificate.certified_iff
    (SchemeRelationCoefficientDiagram.sectionMap p)
    (SchemeRelationCoefficientDiagram.sectionMap q)
    (SchemeRelationCoefficientDiagram.sectionMap r)
    (SchemeRelationCoefficientDiagram.sectionMap s)
    (SchemeRelationCoefficientDiagram.sectionMap i)
    (SchemeRelationCoefficientDiagram.sectionMap z)
    (SchemeRelationCoefficientDiagram.endpoint_square p r i z
      (originalClosedArrow_fst f hL d V c k))
    (SchemeRelationCoefficientDiagram.endpoint_square q s i z
      (originalClosedArrow_snd f hL d V c k)) T (topCoefficientEquiv ec t))
  exact topCoefficient_certified_iff e ec i z
    (originalClosedArrow_fst f hL d V c k) (originalClosedArrow_snd f hL d V c k) t

/-- A certificate on a full ground test returns a finite identity on the original boundary. -/
theorem originalBoundary_certificate_of_ground_test
    (t : (invariantSheaf ec).obj.obj (op ⊤))
    (h : originalClosedGroundSection f hL d V c k T t ∈ sourceCertifiedSections
      (originalClosedGroundMap f hL d V c k T).toRingHom
      (originalClosedGroundInclusion f hL d V c k T)) :
    ∃ a : originalBoundaryLiftIdeal f hL d V c k ⊤ t →₀
        (sourceSheaf ec).obj.obj (op ⊤),
      a.sum (fun v b ↦ b * (invariantInclusion ec).hom.app (op ⊤)
        ((m).c.app (op ⊤) v.val)) = 1 :=
  (mem_originalBoundaryCertifiedSections_iff f hL d V c k ⊤ t).mp
    ((originalBoundaryCertifiedSections_ground_iff f hL d V c k T t).mp h)

/-- The descended identity covers the actual original closed boundary on the affine source. -/
theorem originalBoundary_cover_of_ground_test
    (t : (invariantSheaf ec).obj.obj (op ⊤))
    (h : originalClosedGroundSection f hL d V c k T t ∈ sourceCertifiedSections
      (originalClosedGroundMap f hL d V c k T).toRingHom
      (originalClosedGroundInclusion f hL d V c k T)) :
    (TopologicalSpace.Opens.map (m).base).obj
      (originalBoundaryLiftOpen f hL d V c k ⊤ t) = ⊤ :=
  (mem_originalBoundaryCertifiedSections_iff_cover f hL d V c k ⊤ t
    (originalClosed_top_affine f hL d V c k)).mp
      ((originalBoundaryCertifiedSections_ground_iff f hL d V c k T t).mp h)

end FLT.Mazur.HilbertChart.AffineRestriction
