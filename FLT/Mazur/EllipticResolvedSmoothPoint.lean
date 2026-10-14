/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticFiniteResolvedSpecialization

/-!
# Original points in the actual resolved smooth fiber

The split-depth hypotheses construct every coefficient datum needed for the
finite model. The unrestricted proper specialization then lifts uniquely to
its actual smooth open, preserving both its original inclusion and structure.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] (A : ValuationSubring K)
  {W : WeierstrassCurve A} {π : A} {depth : ℕ} (D : SplitNodeDepth W π depth)

/-- The original split-depth assumptions construct all divided coefficients up to final depth. -/
def splitResolutionData (i : Fin (depth / 2 + 1)) : Data W π (0 + i.val) :=
  Classical.choice (by
    obtain ⟨b3, b4, b6, h3, h4, h6⟩ :=
      WeierstrassDilatation.splitDepth_divided_coefficients D (0 + i.val) (by omega)
    exact ⟨⟨b3, b4, b6, h3, h4, h6⟩⟩)

local notation "k" => ResidueField A
local notation "data" => splitResolutionData A D
local notation "hπ" => SplitNodeDepth.uniformizer_ne_zero D
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap A k))

/-- The actual closed finite model constructed from the original split-depth data. -/
abbrev resolvedSplitFiber := finiteGlobalTensorModel hπ data k (depth / 2) (le_refl _)

/-- Its original residue-field structure morphism. -/
def resolvedSplitStructure : resolvedSplitFiber A D ⟶ Spec (.of k) :=
  pullback.fst q (finiteGlobalStructure hπ data (depth / 2) (le_refl _))

instance resolvedSplitStructure_lfp : LocallyOfFinitePresentation (resolvedSplitStructure A D) :=
  finitePointSpecializationStructure_lfp A hπ data (depth / 2) (le_refl _)

/-- Every original point gives an actual rational point of the resolved smooth fiber. -/
def resolvedSplitSmoothPoint (P : (W.map (algebraMap A K)).toProjective.Point) :
    Spec (.of k) ⟶ (resolvedSplitStructure A D).smoothLocus.toScheme :=
  IsOpenImmersion.lift (resolvedSplitStructure A D).smoothLocus.ι
    (finitePointSpecialization A hπ data (depth / 2) (le_refl _) P) (by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨x, rfl⟩
      exact finitePointSpecialization_resolved_smooth A hπ D data P x)

/-- The smooth point is precisely the original unrestricted proper specialization. -/
@[reassoc] theorem resolvedSplitSmoothPoint_inclusion
    (P : (W.map (algebraMap A K)).toProjective.Point) :
    resolvedSplitSmoothPoint A D P ≫ (resolvedSplitStructure A D).smoothLocus.ι =
      finitePointSpecialization A hπ data (depth / 2) (le_refl _) P :=
  IsOpenImmersion.lift_fac _ _ _

/-- Its structure morphism is the identity on the original residue spectrum. -/
@[reassoc] theorem resolvedSplitSmoothPoint_structure
    (P : (W.map (algebraMap A K)).toProjective.Point) :
    resolvedSplitSmoothPoint A D P ≫ (resolvedSplitStructure A D).smoothLocus.ι ≫
      resolvedSplitStructure A D = 𝟙 _ := by
  rw [← Category.assoc, resolvedSplitSmoothPoint_inclusion]
  exact finitePointSpecialization_structure A hπ data (depth / 2) (le_refl _) P

/-- Passing to the actual smooth open neither identifies nor separates specialized points. -/
theorem resolvedSplitSmoothPoint_eq_iff
    (P Q : (W.map (algebraMap A K)).toProjective.Point) :
    resolvedSplitSmoothPoint A D P = resolvedSplitSmoothPoint A D Q ↔
      finitePointSpecialization A hπ data (depth / 2) (le_refl _) P =
        finitePointSpecialization A hπ data (depth / 2) (le_refl _) Q := by
  rw [← cancel_mono (resolvedSplitStructure A D).smoothLocus.ι,
    resolvedSplitSmoothPoint_inclusion, resolvedSplitSmoothPoint_inclusion]

end FLT.Mazur.WeierstrassDividedDepth
