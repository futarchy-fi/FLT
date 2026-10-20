/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertOriginalScalarTestAtlas
public import FLT.Mazur.SchemeFppfBoundaryCorrections

/-!
# Exact original boundary corrections on the whole scalar-test atlas

The old ambient lifts pull back to the full original scalar-test cover.
Their correction problem is exactly lifting the original boundary value
through the full source equalizer, rather than through a selected chart.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Topology
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve EquivalenceRelationNormalizedFrames
open FiniteGroupRestriction SchemeFiniteGroupQuotient SchemeOpenEnvelope
open RelativeRelationOrbit SchemeScalarPrincipalNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [IsAffine V.left] [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
local notation "p" => Over.Hom.left (fst f hL d V c k)
local notation "q" => Over.Hom.left (snd f hL d V c k)
local notation "e" => fullRelationSchemeEquivalence f hL d V c k
attribute [local irreducible] relation fst snd equivalence

local notation "eo" => equivalence f hL d V c k
variable (W : TopologicalSpace.Opens (Orbit (equivalence f hL d V c k)))
set_option quotPrecheck false
local notation "E" => (pullOpen eo W).val
local notation "Ω" => (invariantSheaf eo).obj.obj (op W)
local notation "s" => orbitScalarCoordinates eo W

attribute [local irreducible] invariantSheaf orbitScalarCoordinates
  EquivalenceRelationNormalizedFrames.source first completeInterior Complete
  scalarMorphism finiteTargetOpen

local notation "ec" => originalClosedEquivalence f hL d V c k
local notation "m" => originalClosedInvariantMap f hL d V c k
local notation "Wc" => (TopologicalSpace.Opens.map (m).base).obj W
attribute [local irreducible] originalClosedEquivalence
  normalizedOriginalBoundaryAction
  normalizedOriginalScalarMap

namespace OriginalScalarSource
open SchemeScalarRelationPullback SchemeFppfRelationDescent InvariantOpenRelationDiagram
open OrbitBoundaryAtlas
attribute [local irreducible] OrbitBoundaryAtlas.finiteCharts
  OrbitBoundaryAtlas.FiniteAtlas.lifts
local notation "Ec" => (pullOpen ec Wc).val
local notation "i" => originalBoundarySourceMap f hL d V c k
local notation "z" => originalClosedArrow f hL d V c k
local notation "g₀" => (openSourceMap eo ec i z
  (originalClosedArrow_fst f hL d V c k) (originalClosedArrow_snd f hL d V c k) W).left
attribute [local irreducible] RelativeRelationOrbit.openSourceMap
  InvariantOpenRelationDiagram.orbitFunctions
variable {Y : Scheme} (b : Y ⟶ Spec (.of
  ((invariantSheaf (equivalence f hL d V c k)).obj.obj (op W))))
  (hW : IsAffineOpen (pullOpen (equivalence f hL d V c k) W).val)
local notation "Old" => finiteCharts f hL d V c k W hW
local notation "oldMap" a:max => OrbitBoundaryAtlas.chartMap f hL d V c k W (a).val
local notation "C" => atlas f hL d V c k W b hW
local notation "iₜ" => testFirst g₀ (scalarMorphism s) b
local notation "pₜ" => testFirst (first f hL d V c k W) (scalarMorphism s) b
local notation "qₜ" => testSecond (first f hL d V c k W) (second f hL d V c k W)
  (scalarMorphism s) (scalar_square f hL d V c k W) b

/-- The prescribed old coefficient on each member of the full scalar-test atlas. -/
def oldTestLift (t : (invariantSheaf ec).obj.obj (op Wc))
    (a : Old) : Γ((C).X a, ⊤) :=
  (pullback.snd (pullback.fst (scalarMorphism s) b) (oldMap a)).appTop
    (OrbitBoundaryAtlas.FiniteAtlas.lifts f hL d V c k W hW t a).val

/-- The unchanged original boundary section pulled to its entire scalar-test source. -/
def originalTestBoundaryValue (t : (invariantSheaf ec).obj.obj (op Wc)) :
    Γ(pullback (g₀ ≫ scalarMorphism s) b, ⊤) :=
  (pullback.fst (g₀ ≫ scalarMorphism s) b).appTop (orbitFunctions ec Wc t).val

/-- The old test coefficients have the exact boundary on the entire old test atlas. -/
theorem oldTestLift_boundary (t : (invariantSheaf ec).obj.obj (op Wc)) :
    HasBoundary C iₜ (oldTestLift f hL d V c k W b hW t)
      (originalTestBoundaryValue f hL d V c k W b t) := by
  unfold HasBoundary oldTestLift originalTestBoundaryValue
  intro a
  let u := pullback.snd iₜ ((C).f a) ≫
    pullback.snd (pullback.fst (scalarMorphism s) b) (oldMap a)
  let w := pullback.fst iₜ ((C).f a) ≫ pullback.fst (g₀ ≫ scalarMorphism s) b
  have hu : u ≫ oldMap a = w ≫ g₀ := by
    dsimp only [u, w]
    rw [Category.assoc,
      ← pullback.condition (f := pullback.fst (scalarMorphism s) b) (g := oldMap a),
      ← Category.assoc]
    change (pullback.snd iₜ ((C).f a) ≫ (C).f a) ≫ pullback.fst (scalarMorphism s) b = _
    rw [← pullback.condition, Category.assoc, testFirst_fst]
    simp only [Category.assoc]
  have h := OrbitBoundaryAtlas.FiniteAtlas.boundary_chart_test f hL d V c k W hW t
    (OrbitBoundaryAtlas.FiniteAtlas.lifts f hL d V c k W hW t) a
    (OrbitBoundaryAtlas.FiniteAtlas.lifts_restrict f hL d V c k W hW t a) u w hu
  simp only [← ConcreteCategory.comp_apply, ← Scheme.Hom.comp_appTop]
  exact h

/-- Exact corrections on the whole test atlas are equivalent to an original test lift. -/
theorem originalTest_lift_iff_corrections (t : (invariantSheaf ec).obj.obj (op Wc)) :
    (∃ v : testRing f hL d V c k W b,
      (iₜ).appTop v.val = originalTestBoundaryValue f hL d V c k W b t) ↔
      ∃ corrections : ∀ a, Γ((C).X a, ⊤),
        (∀ a, (pullback.snd iₜ ((C).f a)).appTop (corrections a) = 0) ∧
        Compatible pₜ qₜ C (fun a ↦ oldTestLift f hL d V c k W b hW t a - corrections a) := by
  let er := fullEquivalence f hL d V c k W
  exact lift_iff_boundary_corrections pₜ qₜ C iₜ
    (testReflexivity _ _ b er.r er.reflexivity₁)
    (testReflexivity_first _ _ b er.r er.reflexivity₁)
    (testReflexivity_second _ _ _ _ b er.r er.reflexivity₁ er.reflexivity₂)
    _ _ (oldTestLift_boundary f hL d V c k W b hW t)

end OriginalScalarSource
end FLT.Mazur.HilbertChart.AffineRestriction
