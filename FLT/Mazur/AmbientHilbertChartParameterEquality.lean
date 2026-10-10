/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AmbientHilbertChartSupport
public import FLT.Mazur.AmbientHilbertOverlapParameterFamily

/-!
# Cross-chart uniqueness of full Hilbert parameters

Equal full families force both affine parameters into their actual common
Hilbert overlap. The constructed transition then identifies their morphisms
into the glued Hilbert scheme.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace FLT.Mazur.HilbertChart.AmbientQuotientCharts

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] {Z : Scheme.{u}} {z : Z ⟶ Spec (.of R)}
variable (A : AmbientQuotientCharts R z) (d : ℕ) [IsSeparated z]
variable {X : Scheme.{u}} (s : X ⟶ Spec (.of R)) (i j : A.Index)
variable (p : AmbientSchemeParameters R (A.Vars i) d (A.relations i) s)
variable (q : AmbientSchemeParameters R (A.Vars j) d (A.relations j) s)

/-- Equal full chart families force the first parameter into the actual common overlap. -/
theorem chartParameter_range_overlap
    (h : A.chartParameterFamily d s i p = A.chartParameterFamily d s j q) :
    Set.range p.val ⊆ A.overlap d i j := by
  apply (A.chartParameterFamily_support_iff d s i p (A.common i j)).mpr
  intro x hx
  change x ∈ (A.chart i).opensRange ∧ x ∈ (A.chart j).opensRange
  refine ⟨A.chartParameterFamily_originalSupport d s i p hx, ?_⟩
  rw [h] at hx
  exact A.chartParameterFamily_originalSupport d s j q hx

/-- Equal full families in arbitrary original affine charts give the same glued parameter. -/
theorem chartParameter_eq_of_family_eq
    (h : A.chartParameterFamily d s i p = A.chartParameterFamily d s j q) :
    A.chartParameter d s i p = A.chartParameter d s j q := by
  let o := IsOpenImmersion.lift (A.overlap d i j).ι p.val
    (by rw [Scheme.Opens.range_ι]; exact A.chartParameter_range_overlap d s i j p q h)
  have ho : o ≫ (A.overlap d i j).ι = p.val := IsOpenImmersion.lift_fac _ _ _
  have hos : o ≫ A.overlapBase d i j = s := by
    rw [overlapBase, ← Category.assoc, ho]
    exact p.property
  let p' : AmbientSchemeParameters R (A.Vars i) d (A.relations i) s :=
    ⟨o ≫ (A.overlap d i j).ι, (Category.assoc _ _ _).trans hos⟩
  let q' : AmbientSchemeParameters R (A.Vars j) d (A.relations j) s :=
    ⟨o ≫ (A.transition d i j).hom ≫ (A.overlap d j i).ι, by
      rw [Category.assoc, Category.assoc, A.transition_over]
      exact hos⟩
  have hp : p' = p := Subtype.ext ho
  have hq : q' = q := by
    apply A.chartParameterFamily_injective d s j
    exact (A.chartParameterFamily_overlap d s i j o hos).trans
      ((congrArg (A.chartParameterFamily d s i) hp).trans h)
  apply Subtype.ext
  change p.val ≫ A.hilbertChart d i = q.val ≫ A.hilbertChart d j
  rw [← hp, ← hq]
  change (o ≫ (A.overlap d i j).ι) ≫ A.hilbertChart d i =
    (o ≫ (A.transition d i j).hom ≫ (A.overlap d j i).ι) ≫ A.hilbertChart d j
  simp only [Category.assoc, A.hilbertChart_overlap]

end FLT.Mazur.HilbertChart.AmbientQuotientCharts
