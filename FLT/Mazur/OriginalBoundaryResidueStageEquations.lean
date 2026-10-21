/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalBoundaryFieldStageEquations

/-!
# Actual original residue tests detected by finite-stage equation witnesses

Local comparison coverage is tested by full endpoint equations on the actual
residue fields. The criterion takes no preselected common-stage factors.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [Etale q] [IsLocallyNoetherian A] [IsAffine A]
  [LocallyQuasiFinite p] (e : CategoryTheory.EquivalenceRelation p q)
local instance residueEquationOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance residueEquationOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance residueEquationOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
variable (J : A.IdealSheafData)

open RingPairInvariantFlatScalars SchemeScalarPrincipalNeighborhood
attribute [local instance] sourceAlgebra targetAlgebra originalBoundaryAlgebra
set_option quotPrecheck false
local notation "R" => invariants p.appTop.hom q.appTop.hom
local notation "f₀" => scalarMorphism (algebraMap R Γ(J.subscheme, ⊤))
local notation "I" n:max a:max ha:max k:max => rankStageCoreBoundaryIdeal e n a ha J k
local notation "g" n:max a:max ha:max k:max => rankStageCoreOriginalBoundaryMap e n a ha J k
variable (hJ : J.comap p = J.comap q)
attribute [local irreducible] rankStageCore rankStageCoreBoundaryIdeal
  rankStageCoreOriginalBoundaryMap rankStageBoundaryOriginalScalars originalBoundaryKernelImage

open SchemeScalarImageQuotient
local notation "m" => originalBoundaryKernelImage p q J
local notation "c₀" => originalBoundaryComparison p q J hJ
variable (U : (Spec (.of (Scalars (scalarMorphism
    (algebraMap (invariants p.appTop.hom q.appTop.hom) Γ(J.subscheme, ⊤)))))).Opens)
local notation "W" => m ⁻¹ᵁ U
local notation "t" w:max => (W).toScheme.fromSpecResidueField w ≫ (W).ι
variable [Etale ((projection (scalarMorphism
    (algebraMap (invariants p.appTop.hom q.appTop.hom) Γ(J.subscheme, ⊤)))) ∣_ U)]

/-- Actual residue-field coverage is exactly a full finite-stage endpoint equation witness. -/
theorem originalBoundary_mem_range_iff_residue_stage_equations (w : (W).toScheme) :
    w.val ∈ Set.range c₀ ↔
    ∃ (n : ℕ) (a : Γ(A, ⊤)) (ha : A.basicOpen a ≤ rankImageOpen (Over.mk p) n)
      (k : ℕ) (x y : Spec ((W).toScheme.residueField w) ⟶ (I n a ha k).subscheme)
      (hx : x ≫ g n a ha k = (t w) ≫ pullback.fst f₀ f₀)
      (hy : y ≫ g n a ha k = (t w) ≫ pullback.snd f₀ f₀),
      rankStageOriginalTestEquations e n a ha J hJ k (t w) x y hx hy := by
  refine Iff.trans ?_ (originalBoundary_field_arrow_iff_exists_stage_equations
    e J hJ (K := (W).toScheme.residueField w) (t w))
  simpa only [Category.assoc] using!
    (originalBoundary_mem_range_iff_residue_arrow e J hJ U w)

/-- Full original fibers are covered exactly when every actual residue test has a stage witness. -/
theorem originalBoundary_fiber_coverage_iff_residue_stage_equations
    (z : Spec (.of (Scalars f₀))) (hz : z ∈ U) :
    (∀ w : (pullback f₀ f₀ : Scheme), m w = z → w ∈ Set.range c₀) ↔
    ∀ w : (W).toScheme, m w.val = z →
      ∃ (n : ℕ) (a : Γ(A, ⊤)) (ha : A.basicOpen a ≤ rankImageOpen (Over.mk p) n)
        (k : ℕ) (x y : Spec ((W).toScheme.residueField w) ⟶ (I n a ha k).subscheme)
        (hx : x ≫ g n a ha k = (t w) ≫ pullback.fst f₀ f₀)
        (hy : y ≫ g n a ha k = (t w) ≫ pullback.snd f₀ f₀),
        rankStageOriginalTestEquations e n a ha J hJ k (t w) x y hx hy := by
  constructor
  · intro H w hw
    exact (originalBoundary_mem_range_iff_residue_stage_equations e J hJ U w).mp (H w.val hw)
  · intro H w hw
    have hwU : w ∈ W := by change m w ∈ U; rw [hw]; exact hz
    exact (originalBoundary_mem_range_iff_residue_stage_equations e J hJ U ⟨w, hwU⟩).mpr
      (H ⟨w, hwU⟩ hw)

end FLT.Mazur.EquivalenceRelationOrderedFrames
