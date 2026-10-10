/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertCommonOpenRestriction

/-!
# Hilbert charts indexed by original affine ambient charts

Only original affine quotient charts and their coefficient-base equations
are inputs. All Hilbert comparisons are constructed from this geometry.
No covering, family comparison, or gluing assertion is part of the input.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.OpenIdealCover

universe u

namespace FLT.Mazur.HilbertChart

/-- Original quotient charts in a shared ambient scheme over the coefficient ring. -/
structure AmbientQuotientCharts (R : Type u) [CommRing R] {Z : Scheme.{u}}
    (z : Z ⟶ Spec (.of R)) where
  /-- The index set of original ambient charts. -/
  Index : Type u
  /-- Polynomial variables for each original chart. -/
  Vars : Index → Type u
  /-- The ideal presenting each original chart. -/
  relations : ∀ i, Ideal (MvPolynomial (Vars i) R)
  /-- The actual open chart embedding. -/
  chart : ∀ i, Spec (.of (MvPolynomial (Vars i) R ⧸ relations i)) ⟶ Z
  chart_open : ∀ i, IsOpenImmersion (chart i)
  /-- The chart is a morphism over the coefficient scheme. -/
  chart_over : ∀ i, chart i ≫ z =
    Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial (Vars i) R ⧸ relations i)))

attribute [instance] AmbientQuotientCharts.chart_open

namespace AmbientQuotientCharts

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] {Z : Scheme.{u}} {z : Z ⟶ Spec (.of R)}
variable (A : AmbientQuotientCharts R z) (d : ℕ)

/-- The full Hilbert representative of one original affine quotient chart. -/
abbrev hilbert (i : A.Index) : Scheme.{u} :=
  ambientHilbertScheme R (A.Vars i) d (A.relations i)

/-- Families in a chart whose full support lies over an ambient open. -/
def support (i : A.Index) (U : Z.Opens) : (A.hilbert d i).Opens :=
  ambientHilbertSupportOpen R (A.Vars i) d (A.relations i) (A.chart i ⁻¹ᵁ U)

/-- The common ambient open of two original charts. -/
def common (i j : A.Index) : Z.Opens := (A.chart i).opensRange ⊓ (A.chart j).opensRange

/-- Actual support inclusions between Hilbert open charts. -/
def inclusion (i : A.Index) {U V : Z.Opens} (h : U ≤ V) :
    (A.support d i U).toScheme ⟶ (A.support d i V).toScheme :=
  openAmbientHilbertInclusion R (A.Vars i) d (A.relations i) _ _
    ((A.chart i).preimage_mono h)

instance (i : A.Index) {U V : Z.Opens} (h : U ≤ V) :
    IsOpenImmersion (A.inclusion d i h) := by
  unfold inclusion openAmbientHilbertInclusion
  infer_instance

/-- Support inclusions preserve the full ambient Hilbert parameter. -/
@[reassoc (attr := simp)]
theorem inclusion_ι (i : A.Index) {U V : Z.Opens} (h : U ≤ V) :
    A.inclusion d i h ≫ (A.support d i V).ι = (A.support d i U).ι :=
  openAmbientHilbertInclusion_ι ..

/-- Support inclusions compose strictly. -/
@[reassoc]
theorem inclusion_comp (i : A.Index) {U V W : Z.Opens} (h : U ≤ V) (k : V ≤ W) :
    A.inclusion d i h ≫ A.inclusion d i k = A.inclusion d i (h.trans k) :=
  openAmbientHilbertInclusion_trans ..

/-- Support respects common intersections as actual opens of the affine Hilbert scheme. -/
theorem support_inf (i : A.Index) (U V : Z.Opens) :
    A.support d i (U ⊓ V) = A.support d i U ⊓ A.support d i V := by
  unfold support
  rw [Scheme.Hom.preimage_inf, ambientHilbertSupportOpen_inf]

/-- The diagonal overlap is the whole affine Hilbert chart, in every degree. -/
theorem support_common_self (i : A.Index) : A.support d i (A.common i i) = ⊤ := by
  simp only [support, common, inf_idem, Scheme.Hom.preimage_opensRange,
    ambientHilbertSupportOpen_top]

/-- The common-open comparison derived from the original quotient chart embeddings. -/
def comparison (i j : A.Index) (U : Z.Opens)
    (hi : U ≤ (A.chart i).opensRange) (hj : U ≤ (A.chart j).opensRange) :
    (A.support d i U).toScheme ≅ (A.support d j U).toScheme :=
  commonAmbientHilbertIso R (A.Vars i) (A.Vars j) d (A.relations i) (A.relations j)
    z (A.chart i) (A.chart j) (A.chart_over i) (A.chart_over j) U hi hj

/-- The common-open comparison commutes with restriction to a smaller common open. -/
theorem comparison_restrict (i j : A.Index) (U T : Z.Opens)
    (hi : U ≤ (A.chart i).opensRange) (hj : U ≤ (A.chart j).opensRange) (h : T ≤ U) :
    A.inclusion d i h ≫ (A.comparison d i j U hi hj).hom =
      (A.comparison d i j T (h.trans hi) (h.trans hj)).hom ≫ A.inclusion d j h :=
  commonAmbientHilbertIso_restrict R (A.Vars i) (A.Vars j) d
    (A.relations i) (A.relations j) z (A.chart i) (A.chart j)
    (A.chart_over i) (A.chart_over j) U hi hj T h

/-- Original ambient chart geometry proves the common-open Hilbert cocycle. -/
theorem comparison_trans (i j k : A.Index) (U : Z.Opens)
    (hi : U ≤ (A.chart i).opensRange) (hj : U ≤ (A.chart j).opensRange)
    (hk : U ≤ (A.chart k).opensRange) :
    A.comparison d i j U hi hj ≪≫ A.comparison d j k U hj hk =
      A.comparison d i k U hi hk := commonAmbientHilbertIso_trans ..

/-- Comparing a common open in one chart with itself is the identity. -/
theorem comparison_self (i : A.Index) (U : Z.Opens) (hi : U ≤ (A.chart i).opensRange) :
    A.comparison d i i U hi hi = Iso.refl _ := by
  apply Iso.ext
  apply (cancel_epi (A.comparison d i i U hi hi).hom).mp
  rw [Iso.refl_hom, Category.comp_id]
  exact congrArg Iso.hom (A.comparison_trans d i i i U hi hi hi)

end AmbientQuotientCharts

end FLT.Mazur.HilbertChart
