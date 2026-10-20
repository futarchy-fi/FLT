/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStageBoundedCoreCover
public import FLT.Mazur.HilbertOrbitBoundaryFiniteAtlas
public import FLT.Mazur.AffineHilbertDerivedNoetherianRelation

/-!
# Coherent original rank cores covering every old Hilbert chart point

No scalar fiber finiteness is assumed. One finite family at finitely many
original ranks covers the entire original orbit domain, hence every point
of every selected old chart. Distinct domains can use distinct cores.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve EquivalenceRelationNormalizedFrames
open RelativeRelationOrbit InvariantOpenRelationDiagram
open FiniteGroupRestriction SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] relativeFppfSheaf AmpleLineBundle
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [IsAffine V.left] [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
attribute [local irreducible] relation fst snd equivalence
  EquivalenceRelationNormalizedFrames.source
namespace OrbitBoundaryAtlas.FiniteAtlas
attribute [local irreducible] finiteCharts
local notation "e" => equivalence f hL d V c k
variable (W : TopologicalSpace.Opens (Orbit (equivalence f hL d V c k)))
set_option quotPrecheck false
local notation "E" => (pullOpen e W).val

variable (hW : IsAffineOpen (pullOpen (equivalence f hL d V c k) W).val)
local notation "C" => finiteCharts f hL d V c k W hW

local notation "p" => Over.Hom.left (AffineRestriction.fst f hL d V c k)
local notation "q" => Over.Hom.left (AffineRestriction.snd f hL d V c k)

open RelativeOrderedTuples EquivalenceRelationOrderedFrames
local notation "ef" => fullRelationSchemeEquivalence f hL d V c k
local instance hilbertCoverOver_separated : IsSeparated (Over.mk p).hom :=
  inferInstanceAs (IsSeparated p)
local instance hilbertCoverOver_etale : Etale (Over.mk p).hom := inferInstanceAs (Etale p)
local instance hilbertCoverOver_compact : QuasiCompact (Over.mk p).hom :=
  inferInstanceAs (QuasiCompact p)

/-- All original chart points are covered, with their exact original rank retained. -/
theorem exists_oldAtlas_bounded_original_core_cover :
    let _ := selectedHilbertSource_isLocallyNoetherian f d V k
    let _ : LocallyQuasiFinite p :=
      LocallyQuasiFinite.of_finite_preimage_singleton _ (fst_finite_fiber f hL d V c k)
    ∃ (N : ℕ) (L : Fin (N + 1) → Finset (Γ(A.left, ⊤) × Γ(A.left, ⊤))),
      (∀ n pair, pair ∈ L n → ∃ ha : A.left.basicOpen pair.1 ≤ rankImageOpen (Over.mk p) n.val,
        A.left.basicOpen pair.2 ≤ E ∧
        A.left.basicOpen pair.2 ≤ rankImageOpen (Over.mk p) n.val ∧
        ∀ order, rankThickeningMap (Over.mk p) n.val order ⁻¹ᵁ A.left.basicOpen pair.2 ≤
          rankStageCore ef n.val pair.1 ha order) ∧
      ∀ (j : C) (x : j.val.domain.toScheme), ∃ n : Fin (N + 1),
        (E).ι (chartMap f hL d V c k W j.val x) ∈ exactRank (Over.mk p) n.val ∧
        ∃ pair ∈ L n, (E).ι (chartMap f hL d V c k W j.val x) ∈ A.left.basicOpen pair.2 := by
  let _ := selectedHilbertSource_isLocallyNoetherian f d V k
  let _ : LocallyQuasiFinite p :=
    LocallyQuasiFinite.of_finite_preimage_singleton _ (fst_finite_fiber f hL d V c k)
  dsimp only
  exact exists_rankStage_bounded_test_core_cover ef E
    (fun j : C ↦ j.val.domain.toScheme)
    (fun j x ↦ (E).ι (chartMap f hL d V c k W j.val x))
    (fun j x ↦ (chartMap f hL d V c k W j.val x).property)

end OrbitBoundaryAtlas.FiniteAtlas
end FLT.Mazur.HilbertChart.AffineRestriction
