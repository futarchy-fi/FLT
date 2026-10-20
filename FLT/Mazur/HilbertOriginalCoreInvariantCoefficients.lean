/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.NormalizedChartCoreInvariantCoefficients
public import FLT.Mazur.HilbertOrbitBoundaryLocalizedMaps
public import FLT.Mazur.HilbertOrbitBoundaryFiniteAtlas
public import FLT.Mazur.AffineHilbertDerivedNoetherianRelation

/-!
# Actual old Hilbert chart invariants from full original core values

The unchanged original chart section is promoted to its actual invariant
coordinate ring using every core order and the full moving-endpoint action.
Existence of a full original representative with these values remains a
separate gluing obligation.
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
local instance hilbertInvariantCoreOver_separated : IsSeparated (Over.mk p).hom :=
  inferInstanceAs (IsSeparated p)
local instance hilbertInvariantCoreOver_etale : Etale (Over.mk p).hom := inferInstanceAs (Etale p)
local instance hilbertInvariantCoreOver_compact : QuasiCompact (Over.mk p).hom :=
  inferInstanceAs (QuasiCompact p)

/-- Every original full section with the prescribed core values is an actual old chart invariant. -/
theorem exists_originalChartInvariantOfCoreValues :
    let _ := selectedHilbertSource_isLocallyNoetherian f d V k
    let _ : LocallyQuasiFinite p :=
      LocallyQuasiFinite.of_finite_preimage_singleton _ (fst_finite_fiber f hL d V c k)
    ∀ {ι : Type} (n : ι → ℕ) (a b : ι → Γ(A.left, ⊤))
      (ha : ∀ i, A.left.basicOpen (a i) ≤ rankImageOpen (Over.mk p) (n i))
      (_ : ∀ i order, rankThickeningMap (Over.mk p) (n i) order ⁻¹ᵁ A.left.basicOpen (b i) ≤
        rankStageCore ef (n i) (a i) (ha i) order)
      (j : C)
      (_ : ∀ x : j.val.domain.toScheme, ∃ i,
        (chartMap f hL d V c k W j.val ≫ (E).ι) x ∈ exactRank (Over.mk p) (n i) ∧
        (chartMap f hL d V c k W j.val ≫ (E).ι) x ∈ A.left.basicOpen (b i))
      (s : Γ(j.val.domain.toScheme, ⊤))
      (w : ∀ i order, rankStageCoreInvariants ef (n i) (a i) (ha i) order),
      (∀ i order,
        (pullback.snd (rankStageCoreOriginalMap ef (n i) (a i) (ha i) order)
          (chartMap f hL d V c k W j.val ≫ (E).ι)).appTop s =
        (pullback.fst (rankStageCoreOriginalMap ef (n i) (a i) (ha i) order)
          (chartMap f hL d V c k W j.val ≫ (E).ι)).appTop (w i order).val) →
      ∃ t : chartCoordinateRing f hL d V c k W hW j, t.val = s := by
  let _ := selectedHilbertSource_isLocallyNoetherian f d V k
  let _ : LocallyQuasiFinite p :=
    LocallyQuasiFinite.of_finite_preimage_singleton _ (fst_finite_fiber f hL d V c k)
  dsimp only
  intro ι n a b ha h j hcover s w hs
  have hc : ∀ x : j.val.domain.toScheme, ∃ i,
      (j.val.domain.ι ≫ normalizedFullRelationFirst f hL d V c k j.val.size j.val.label) x ∈
        exactRank (Over.mk p) (n i) ∧
      (j.val.domain.ι ≫ normalizedFullRelationFirst f hL d V c k j.val.size j.val.label) x ∈
        A.left.basicOpen (b i) := by
    simpa only [chartMap_inclusion] using hcover
  simp only [normalizedFullRelationFirst] at hc
  rw [← @chartCoreCoefficientMap_eq _ _ p q inferInstance
    (Fin j.val.size) inferInstance j.val.label j.val.domain] at hc
  refine ⟨chartInvariantOfCoreValues ef (Fin j.val.size) j.val.label j.val.domain j.val.stable
    n a b ha h hc s w ?_, rfl⟩
  have hg := (chartMap_inclusion f hL d V c k W j.val).trans
    (@chartCoreCoefficientMap_eq _ _ p q inferInstance
      (Fin j.val.size) inferInstance j.val.label j.val.domain).symm
  rw [hg] at hs
  exact hs

end OrbitBoundaryAtlas.FiniteAtlas
end FLT.Mazur.HilbertChart.AffineRestriction
