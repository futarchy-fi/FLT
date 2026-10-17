/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertUniformSourceBoundaryDescent
public import FLT.Mazur.HilbertOrbitBoundaryAtlas
public import FLT.Mazur.RelativeRelationEtaleSourceFunctions

/-!
# The constructed uniform original lifting domain

Each affine atlas chart gives an original orbit neighborhood on which every
boundary section from the fixed domain lifts. Their union is an actual open,
chosen independently of the boundary section. Membership supplies a genuine
local lift; equality of this open with the prescribed domain remains separate.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve EquivalenceRelationNormalizedFrames
open RelativeRelationOrbit InvariantOpenRelationDiagram
open FiniteGroupRestriction SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [IsAffine V.left] [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
local notation "p" => Over.Hom.left (AffineRestriction.fst f hL d V c k)
local notation "q" => Over.Hom.left (AffineRestriction.snd f hL d V c k)
local notation "e" => fullRelationSchemeEquivalence f hL d V c k
local notation "eo" => equivalence f hL d V c k
local notation "ec" => originalClosedEquivalence f hL d V c k
local notation "m" => originalClosedInvariantMap f hL d V c k
attribute [local irreducible] relation AffineRestriction.fst AffineRestriction.snd equivalence
  EquivalenceRelationNormalizedFrames.source relativeFppfSheaf AmpleLineBundle
  originalBoundarySource originalBoundarySourceMap originalClosedRelation
  originalClosedFst originalClosedSnd originalClosedArrow originalClosedEquivalence
namespace OrbitBoundaryAtlas
variable (W : TopologicalSpace.Opens (Orbit (equivalence f hL d V c k)))
attribute [local irreducible] EquivalenceRelationNormalizedFrames.action
  uniformSourceOpen orbitImageOpen etaleSourceImage
set_option quotPrecheck false
local notation "Wc" => (TopologicalSpace.Opens.map (m).base).obj W
local notation "Charts" => Chart f hL d V c k W

/-- The original orbit image of the constructed uniform restriction of an affine atlas chart. -/
def uniformOrbitOpen (a : Charts) : TopologicalSpace.Opens (Orbit eo) :=
  orbitImageOpen eo (q).isOpenMap (etaleSourceImage
    ((uniformSourceOpen e (Fin a.size) a.label a.domain a.stable).ι ≫
      a.domain.ι ≫ normalizedFullRelationFirst f hL d V c k a.size a.label))

/-- Every such orbit neighborhood stays in the original prescribed domain. -/
theorem uniformOrbitOpen_le (a : Charts) : uniformOrbitOpen f hL d V c k W a ≤ W :=
  uniformSource_orbitImage_le f hL d V c k a.size a.label a.domain a.stable W a.overDomain

/-- Every original boundary section has an exact lift on each constructed orbit neighborhood. -/
theorem uniformOrbitOpen_boundary_lift (a : Charts)
    (t : (invariantSheaf ec).obj.obj (op Wc)) :
    ∃ b : (invariantSheaf eo).obj.obj (op (uniformOrbitOpen f hL d V c k W a)),
      (m).c.app (op (uniformOrbitOpen f hL d V c k W a)) b =
        (invariantSheaf ec).obj.map ((TopologicalSpace.Opens.map (m).base).map
          (homOfLE (uniformOrbitOpen_le f hL d V c k W a))).op t :=
  uniformSource_original_boundary_lift f hL d V c k a.size a.label a.domain a.stable
    W a.overDomain a.affine t

/-- The union is constructed from geometry before choosing any boundary section. -/
def uniformLiftingOpen : TopologicalSpace.Opens (Orbit eo) :=
  ⨆ a : Charts, uniformOrbitOpen f hL d V c k W a

/-- The constructed local lifting domain is contained in the unchanged original domain. -/
theorem uniformLiftingOpen_le : uniformLiftingOpen f hL d V c k W ≤ W :=
  iSup_le (uniformOrbitOpen_le f hL d V c k W)

/-- Membership is witnessed by a concrete stable affine chart and its uniform source image. -/
theorem mem_uniformLiftingOpen (x : Orbit eo) :
    x ∈ uniformLiftingOpen f hL d V c k W ↔
      ∃ a : Charts, x ∈ uniformOrbitOpen f hL d V c k W a :=
  TopologicalSpace.Opens.mem_iSup

/-- Every point of the constructed union has one neighborhood lifting all fixed-domain sections. -/
theorem uniformLiftingOpen_neighborhood (x : Orbit eo)
    (hx : x ∈ uniformLiftingOpen f hL d V c k W) :
    ∃ (O : TopologicalSpace.Opens (Orbit eo)) (hOW : O ≤ W), x ∈ O ∧
      ∀ t : (invariantSheaf ec).obj.obj (op Wc),
        ∃ b : (invariantSheaf eo).obj.obj (op O),
          (m).c.app (op O) b = (invariantSheaf ec).obj.map
            ((TopologicalSpace.Opens.map (m).base).map (homOfLE hOW)).op t := by
  obtain ⟨a, ha⟩ := (mem_uniformLiftingOpen f hL d V c k W x).mp hx
  exact ⟨uniformOrbitOpen f hL d V c k W a, uniformOrbitOpen_le f hL d V c k W a,
    ha, uniformOrbitOpen_boundary_lift f hL d V c k W a⟩

end OrbitBoundaryAtlas
end FLT.Mazur.HilbertChart.AffineRestriction
