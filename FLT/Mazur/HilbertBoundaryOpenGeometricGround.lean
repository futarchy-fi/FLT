/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertBoundaryGeometricGround
public import FLT.Mazur.RelativeRelationOpenFunctionMap

/-!
# Geometric boundary tests on every original orbit domain

All four restricted schemes satisfy the geometric comparison hypotheses,
proved from the original Hilbert geometry. The constructed test uses the
entire relation on each orbit domain and returns an actual finite source
identity when its geometric certificate is established.
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

local instance relationNoetherian : IsNoetherian (D).left :=
  fullRelation_isNoetherian f hL d V c k

local instance closedSourceNoetherian : IsNoetherian (B).left := by
  let _ := selectedAffineHilbertSource_isNoetherian f d V k
  let _ := LocallyOfFiniteType.isLocallyNoetherian (i).left
  exact ⟨⟩

local instance closedRelationNoetherian : IsNoetherian (C).left := by
  let _ := LocallyOfFiniteType.isLocallyNoetherian (z).left
  exact ⟨⟩

attribute [local irreducible] originalBoundarySource originalBoundarySourceMap
  originalClosedRelation originalClosedFst originalClosedSnd originalClosedArrow
  originalClosedEquivalence relation fst snd equivalence

variable (W : TopologicalSpace.Opens (Orbit (equivalence f hL d V c k)))
set_option quotPrecheck false
local notation "Wc" => (TopologicalSpace.Opens.map (m).base).obj W
local notation "U" => (pullOpen e W).val
local notation "Uc" => (pullOpen ec Wc).val
local notation "hp" => originalClosedArrow_fst f hL d V c k
local notation "hq" => originalClosedArrow_snd f hL d V c k

/-- Every original source orbit domain is compact, by the actual Noetherian source. -/
instance originalOpenGround_source_compact :
    CompactSpace (InvariantOpenRelationDiagram.source U).left := by
  let _ := selectedAffineHilbertSource_isNoetherian f d V k
  let _ : TopologicalSpace.NoetherianSpace A.left := inferInstance
  let _ : TopologicalSpace.NoetherianSpace U :=
    TopologicalSpace.NoetherianSpace.set (U : Set A.left)
  exact TopologicalSpace.NoetherianSpace.compactSpace U

/-- The entire relation on every original orbit domain is compact. -/
instance originalOpenGround_relation_compact :
    CompactSpace (InvariantOpenRelationDiagram.relation p U).left := by
  let _ : TopologicalSpace.NoetherianSpace (D).left := inferInstance
  let _ : TopologicalSpace.NoetherianSpace ((p).left ⁻¹ᵁ U) :=
    TopologicalSpace.NoetherianSpace.set (((p).left ⁻¹ᵁ U) : Set (D).left)
  exact TopologicalSpace.NoetherianSpace.compactSpace ((p).left ⁻¹ᵁ U)

/-- The actual closed boundary on every original orbit domain is compact. -/
instance originalOpenGround_boundary_compact :
    CompactSpace (InvariantOpenRelationDiagram.source Uc).left := by
  let _ : TopologicalSpace.NoetherianSpace (B).left := inferInstance
  let _ : TopologicalSpace.NoetherianSpace Uc :=
    TopologicalSpace.NoetherianSpace.set (Uc : Set (B).left)
  exact TopologicalSpace.NoetherianSpace.compactSpace Uc

/-- The entire closed relation on every original orbit domain is compact. -/
instance originalOpenGround_closedRelation_compact :
    CompactSpace (InvariantOpenRelationDiagram.relation r Uc).left := by
  let _ : TopologicalSpace.NoetherianSpace (C).left := inferInstance
  let _ : TopologicalSpace.NoetherianSpace ((r).left ⁻¹ᵁ Uc) :=
    TopologicalSpace.NoetherianSpace.set (((r).left ⁻¹ᵁ Uc) : Set (C).left)
  exact TopologicalSpace.NoetherianSpace.compactSpace ((r).left ⁻¹ᵁ Uc)

attribute [local instance] SchemeFunctionGroundChange.sectionAlgebra
open SchemeFunctionGroundChange CanonicalSchemeRelationGround
open InvariantOpenRelationDiagram hiding fst snd relation
variable {T : Scheme} [IsAffine T] (g : T ⟶ Spec (.of R)) [Flat g] [Surjective g]
local notation "rg" => groundMap g (InvariantOpenRelationDiagram.fst r Uc)
local notation "sg" => groundMap g (InvariantOpenRelationDiagram.snd r s Uc
  (pullOpen_preimage_eq ec Wc))

/-- The actual boundary section on the canonical geometric test of its orbit domain. -/
def originalBoundaryOpenGeometricSection
    (t : (invariantSheaf ec).obj.obj (op Wc)) :
    AlgHom.equalizer (sectionMap rg) (sectionMap sg) := by
  exact @openGeometricSection _ _ _ _ _ _ _ _ _ e ec i z hp hq W
    inferInstance inferInstance
    (originalOpenGround_boundary_compact f hL d V c k W)
    (originalOpenGround_closedRelation_compact f hL d V c k W)
    T inferInstance inferInstance g inferInstance t

/-- Geometric testing on any orbit domain detects its original finite source certificate. -/
theorem originalBoundaryOpenCertified_geometric_iff
    (t : (invariantSheaf ec).obj.obj (op Wc)) :
    originalBoundaryOpenGeometricSection f hL d V c k W g t ∈ sourceCertifiedSections
      (openGeometricFunctionMap e ec i z hp hq W g).toRingHom
      (AlgHom.equalizer (sectionMap rg) (sectionMap sg)).val.toRingHom ↔
    t ∈ originalBoundaryCertifiedSections f hL d V c k W := by
  exact @openGeometric_certified_iff _ _ _ _ _ _ _ _ _ e ec i z hp hq W
    inferInstance inferInstance inferInstance inferInstance
    (originalOpenGround_source_compact f hL d V c k W)
    (originalOpenGround_relation_compact f hL d V c k W)
    (originalOpenGround_boundary_compact f hL d V c k W)
    (originalOpenGround_closedRelation_compact f hL d V c k W)
    T inferInstance inferInstance g inferInstance inferInstance t

/-- The geometric certificate produces the actual finite identity on the original open source. -/
theorem originalBoundary_open_certificate_of_geometric_test
    (t : (invariantSheaf ec).obj.obj (op Wc))
    (ht : originalBoundaryOpenGeometricSection f hL d V c k W g t ∈ sourceCertifiedSections
      (openGeometricFunctionMap e ec i z hp hq W g).toRingHom
      (AlgHom.equalizer (sectionMap rg) (sectionMap sg)).val.toRingHom) :
    ∃ a : originalBoundaryLiftIdeal f hL d V c k W t →₀
        (sourceSheaf ec).obj.obj (op Wc),
      a.sum (fun v b ↦ b * (invariantInclusion ec).hom.app (op Wc)
        ((m).c.app (op W) v.val)) = 1 :=
  (mem_originalBoundaryCertifiedSections_iff f hL d V c k W t).mp
    ((originalBoundaryOpenCertified_geometric_iff f hL d V c k W g t).mp ht)

/-- On an affine source domain the tested identity covers the actual original boundary. -/
theorem originalBoundary_open_cover_of_geometric_test
    (t : (invariantSheaf ec).obj.obj (op Wc)) (hW : IsAffineOpen U)
    (ht : originalBoundaryOpenGeometricSection f hL d V c k W g t ∈ sourceCertifiedSections
      (openGeometricFunctionMap e ec i z hp hq W g).toRingHom
      (AlgHom.equalizer (sectionMap rg) (sectionMap sg)).val.toRingHom) :
    (TopologicalSpace.Opens.map (m).base).obj
      (originalBoundaryLiftOpen f hL d V c k W t) = Wc :=
  (mem_originalBoundaryCertifiedSections_iff_cover f hL d V c k W t hW).mp
    ((originalBoundaryOpenCertified_geometric_iff f hL d V c k W g t).mp ht)

end FLT.Mazur.HilbertChart.AffineRestriction
