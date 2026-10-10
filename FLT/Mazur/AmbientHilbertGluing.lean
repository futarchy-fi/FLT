/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AmbientHilbertTripleRoutes
public import FLT.Mazur.OpenAtlasTripleGluing

/-!
# The glued Hilbert scheme of original affine ambient charts

Actual quotient chart embeddings construct pair transitions, full triple
routes, and the categorical rotation cocycle. These assemble a scheme gluing
datum and its glued scheme. The original affine Hilbert schemes form an open
cover of the result. Coverage of all families still requires the separate
common-affine-neighborhood argument.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace FLT.Mazur.HilbertChart.AmbientQuotientCharts

variable {R : Type u} [CommRing R] {Z : Scheme.{u}} {z : Z ⟶ Spec (.of R)}
variable (A : AmbientQuotientCharts R z) (d : ℕ)

/-- The actual Hilbert gluing datum, constructed solely from original ambient charts. -/
def hilbertGlueData : Scheme.GlueData.{u} where
  J := A.Index
  U := A.hilbert d
  V p := (A.overlap d p.1 p.2).toScheme
  f i j := (A.overlap d i j).ι
  f_id i := by
    rw [A.overlap_self]
    exact (A.hilbert d i).topIso.isIso_hom
  t i j := (A.transition d i j).hom
  t_id := A.transition_self d
  t' := openAtlasTripleRotate (A.hilbert d) (A.overlap d) (A.transition d)
    (A.tripleRoute d) (A.tripleRoute_first d)
  t_fac := openAtlasTripleRotate_snd (A.hilbert d) (A.overlap d) (A.transition d)
    (A.tripleRoute d) (A.tripleRoute_first d)
  cocycle := openAtlasTripleRotate_cocycle (A.hilbert d) (A.overlap d) (A.transition d)
    (A.tripleRoute d) (A.tripleRoute_first d) (A.tripleRoute_second d)
    (A.transition_inverse d)
  f_open _ _ := inferInstance

/-- The scheme obtained by gluing the actual affine ambient Hilbert charts. -/
def gluedHilbert : Scheme.{u} := (A.hilbertGlueData d).glued

/-- Each original affine Hilbert chart embeds into the constructed scheme. -/
def hilbertChart (i : A.Index) : A.hilbert d i ⟶ A.gluedHilbert d :=
  (A.hilbertGlueData d).ι i

instance (i : A.Index) : IsOpenImmersion (A.hilbertChart d i) := by
  exact Scheme.GlueData.ι_isOpenImmersion (A.hilbertGlueData d) i

/-- The affine Hilbert charts cover the constructed scheme. -/
def hilbertOpenCover : Scheme.OpenCover (A.gluedHilbert d) :=
  (A.hilbertGlueData d).openCover

/-- Every point of the glued Hilbert scheme comes from an original affine Hilbert chart. -/
theorem hilbertChart_jointly_surjective (x : A.gluedHilbert d) :
    ∃ i, ∃ y : A.hilbert d i, A.hilbertChart d i y = x :=
  (A.hilbertGlueData d).ι_jointly_surjective x

end FLT.Mazur.HilbertChart.AmbientQuotientCharts
