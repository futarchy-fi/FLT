/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ChowAffineBaseChartData
public import FLT.Mazur.ChowSourceClosure
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-!
# The common-open source closure over a Noetherian affine base

Stacks 0200 first replaces the source by the scheme-theoretic image of its
dense common open. We construct that closed subscheme, prove that it is
proper and surjective over the original source, and construct its inverse
isomorphism over the common open. The common open is scheme-theoretically
dense in this replacement, with no reducedness assumption.

This is the source-replacement step, preceding the graph closure modification.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

universe u

set_option backward.isDefEq.respectTransparency false

namespace FLT.Mazur.Chow.AffineBase

variable {R : CommRingCat.{u}} {X : Scheme.{u}} {f : X ⟶ Spec R}

namespace ChartData

variable (D : ChartData f)

/-- The closed subscheme defined by the kernel ideal sheaf of the common-open
inclusion, retaining all scheme structure. -/
def sourceClosure : Scheme.{u} := D.common.ι.image

/-- The canonical closed immersion into the original source. -/
def sourceClosureι : D.sourceClosure ⟶ X := D.common.ι.imageι

instance sourceClosureι_isClosedImmersion : IsClosedImmersion D.sourceClosureι := by
  dsimp [sourceClosureι]
  infer_instance

instance sourceClosureι_isProper : IsProper D.sourceClosureι := by
  dsimp [sourceClosureι]
  infer_instance

/-- The original common open factors through its scheme-theoretic closure. -/
def commonToSourceClosure : D.common.toScheme ⟶ D.sourceClosure := D.common.ι.toImage

@[reassoc (attr := simp)]
lemma commonToSourceClosure_ι :
    D.commonToSourceClosure ≫ D.sourceClosureι = D.common.ι :=
  D.common.ι.toImage_imageι

/-- The scheme-theoretic closure changes nothing over the common open. -/
instance sourceClosure_restrict_isIso : IsIso (D.sourceClosureι ∣_ D.common) :=
  openImage_restrict_isIso D.common

/-- The actual comparison isomorphism over the original common open. -/
def sourceClosureCommonIso :
    (D.sourceClosureι ⁻¹ᵁ D.common).toScheme ≅ D.common.toScheme :=
  asIso (D.sourceClosureι ∣_ D.common)

@[reassoc (attr := simp)]
lemma sourceClosureCommonIso_hom_ι :
    D.sourceClosureCommonIso.hom ≫ D.common.ι =
      (D.sourceClosureι ⁻¹ᵁ D.common).ι ≫ D.sourceClosureι :=
  morphismRestrict_ι D.sourceClosureι D.common

/-- The original affine chart cover pulls back to affine opens of the closure. -/
lemma sourceClosure_affine (i : D.Index) :
    IsAffineOpen (D.sourceClosureι ⁻¹ᵁ D.opens i) :=
  (D.affine i).preimage D.sourceClosureι

/-- The pulled-back affine charts cover the constructed source closure. -/
lemma sourceClosure_covers : (⨆ i, D.sourceClosureι ⁻¹ᵁ D.opens i) = ⊤ := by
  rw [← Scheme.Hom.preimage_iSup, D.covers, Scheme.Hom.preimage_top]

variable [IsNoetherianRing R] [LocallyOfFiniteType f] [QuasiCompact f]

instance commonToSourceClosure_isOpenImmersion : IsOpenImmersion D.commonToSourceClosure := by
  let _noetherian := source_isNoetherian f
  change IsOpenImmersion D.common.ι.toImage
  infer_instance

instance commonToSourceClosure_schemeTheoreticallyDominant :
    IsSchemeTheoreticallyDominant D.commonToSourceClosure := by
  let _noetherian := source_isNoetherian f
  exact toImage_schemeTheoreticallyDominant D.common.ι

/-- Topological density of the common open makes the closed replacement
surjective, without identifying its ideal sheaf with the zero ideal. -/
lemma sourceClosureι_surjective : Function.Surjective D.sourceClosureι := by
  let _noetherian := source_isNoetherian f
  rw [← Set.range_eq_univ]
  change Set.range D.common.ι.ker.subschemeι = Set.univ
  rw [Scheme.IdealSheafData.range_subschemeι, Scheme.Hom.support_ker,
    Scheme.Opens.range_ι]
  exact D.common_dense.closure_eq

end ChartData

end FLT.Mazur.Chow.AffineBase
