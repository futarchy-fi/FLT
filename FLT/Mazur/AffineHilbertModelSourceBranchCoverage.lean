/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertModelEtaleBranchCoverage
public import FLT.Mazur.KernelPairGenericBranchInverses

/-!
# Original Picard points from a propagated source branch

The proper-family relation supplies both etale endpoints and a monomorphic
kernel comparison. A single nonempty two-sided etale source branch and point
coverage of the full generic kernel then construct a represented original
source point. No generic inverse morphisms or reducedness are inputs.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve
attribute [local irreducible] relation fst snd
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
local notation "p" => Over.Hom.left (fst f hL d V c k)
local notation "q" => Over.Hom.left (snd f hL d V c k)
variable {T : Over (Spec (.of R))} (w : A ⟶ T)
  [IsNoetherian T.left] [IrreducibleSpace T.left]
  [LocallyOfFinitePresentation w.left] [QuasiCompact w.left]
  {Z : Scheme} (a : Z ⟶ A.left) [Etale a] [Etale (a ≫ w.left)] [Nonempty Z]
local notation "M" => modelRelationKernelMap f hL d V c k w.left
local notation "v" => pullback.fst w.left w.left ≫ w.left

include a

/-- The full actual kernel gets inverse neighborhoods by propagating an unrestricted branch. -/
theorem modelEffectiveTarget_nonempty_of_source_branch
    (hw : p ≫ w.left = q ≫ w.left)
    (hg : ∀ x : (pullback w.left w.left : Scheme),
      v x = genericPoint T.left → x ∈ Set.range (fun r : (relation f hL d V c k).left ↦ M hw r)) :
    Nonempty (modelEffectiveTarget f hL d V c k w hw).left := by
  let _ : Mono (pullback.lift p q hw) := modelRelationKernelMap_mono f hL d V c k w.left hw
  let _ : IsNoetherian A.left := by
    let _ := selectedHilbertSource_isLocallyNoetherian f d V k
    exact ⟨⟩
  obtain ⟨y, hy⟩ := KernelPairEffectiveOpen.targetOpen_nonempty_of_source_branch
    p q w.left hw a hg
  exact ⟨⟨y, hy⟩⟩

/-- The resulting point belongs to the represented original Picard source, not just its model. -/
theorem modelFppfSource_nonempty_of_source_branch
    (hw : p ≫ w.left = q ≫ w.left)
    (hg : ∀ x : (pullback w.left w.left : Scheme),
      v x = genericPoint T.left → x ∈ Set.range (fun r : (relation f hL d V c k).left ↦ M hw r)) :
    Nonempty (modelFppfSource f hL d V c k w hw).left := by
  have he := modelEffectiveTarget_nonempty_of_source_branch f hL d V c k w a hw hg
  obtain ⟨y⟩ := modelFppfTarget_nonempty_of_etale_branch f hL d V c k w hw a he
  obtain ⟨x, _⟩ := (modelFppfProjection f hL d V c k w hw).left.surjective y
  exact ⟨x⟩

end FLT.Mazur.HilbertChart.AffineRestriction
