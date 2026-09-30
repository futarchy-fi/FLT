/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ChowChartData
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-!
# The scheme-theoretic closure of the common Chow open

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

namespace FLT.Mazur.Chow

/-- A quasi-compact morphism is scheme-theoretically dominant onto its actual
scheme-theoretic image. -/
lemma toImage_schemeTheoreticallyDominant {Y Z : Scheme.{u}} (g : Y ⟶ Z)
    [QuasiCompact g] : IsSchemeTheoreticallyDominant g.toImage := by
  constructor
  apply Scheme.IdealSheafData.ext_of_iSup_eq_top
    (fun V : Z.affineOpens ↦ ⟨g.imageι ⁻¹ᵁ V, V.2.preimage g.imageι⟩)
  · simp only [← Scheme.Hom.preimage_iSup, iSup_affineOpens_eq_top,
      Scheme.Hom.preimage_top]
  · intro V
    rw [Scheme.Hom.ker_apply, Scheme.IdealSheafData.ideal_bot]
    exact (RingHom.injective_iff_ker_eq_bot _).mp (g.toImage_app_injective V)

/-- The closed image of an open inclusion restricts to an isomorphism over
that open: the pullback projection has a constructed section and is mono. -/
lemma openImage_restrict_isIso {Y : Scheme.{u}} (V : Y.Opens) :
    IsIso (V.ι.imageι ∣_ V) := by
  let s : V.toScheme ⟶ pullback V.ι.imageι V.ι :=
    pullback.lift V.ι.toImage (𝟙 _) (by simp)
  let _split : IsSplitEpi (pullback.snd V.ι.imageι V.ι) :=
    IsSplitEpi.mk' ⟨s, by simp [s]⟩
  let _iso := isIso_of_mono_of_isSplitEpi (pullback.snd V.ι.imageι V.ι)
  unfold morphismRestrict
  infer_instance

variable {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (.of k)}

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

variable [LocallyOfFiniteType f] [QuasiCompact f]

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

end FLT.Mazur.Chow
