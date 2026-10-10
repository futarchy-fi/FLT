/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AmpleCommonDegree
public import FLT.Mazur.AmplePreimageSectionCover
public import FLT.Mazur.FiniteCompactOpenCoverLimit
public import FLT.Mazur.LinePowerSectionLimitDescent
public import FLT.Mazur.LineSectionOpenCompact

/-!
# Descending ampleness of a specified line through an inverse limit

Choose a common-degree affine section cover on the limit, descend its actual
coordinates, then descend affineness and coverage of the recovered generator
opens. The resulting ample line is the pullback of the specified stage line.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry
open CategoryTheory.Limits (Cone IsLimit)
open Scheme.Modules FLT.Mazur.FCurve FLT.Mazur.FCurve.ModuleLineBundleTensorPullback

namespace FLT.Mazur.Approximation

universe u

variable {I : Type u} [Category.{u} I] [IsCofiltered I]
  (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
  [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
  [∀ i, QuasiSeparatedSpace (D.obj i)] [∀ i, CompactSpace (D.obj i)]

include hc in
/-- Ampleness on the limit descends for the chosen finite-stage line sheaf. -/
theorem exists_ampleLineBundle_of_limit (i : I) [(D.obj i).IsSeparated]
    (L : (D.obj i).Modules) (hL : LocallyFreeRankOne L)
    (hA : AmpleLineBundle ((pullback (c.π.app i)).obj L)) :
    ∃ (j : I) (f : j ⟶ i), AmpleLineBundle ((pullback (D.map f)).obj L) := by
  obtain ⟨T, hT, n, hn, s, haff, hcover⟩ := hA.common_degree_section_cover
  let _ := hT
  obtain ⟨ι, hι, U, hUaff, he, hU⟩ := (hL.tensorPower n).finite_affine_trivializing_cover
  let _ := hι
  have hcompact (a : NonemptyChartSet ι) :
      IsCompact (finiteIntersectionOpen U a : Set (D.obj i)) := by
    have ha : IsAffineOpen (finiteIntersectionOpen U a) :=
      finiteIntersectionSchemeDiagram_isAffine U hUaff (.op a)
    exact ha.isCompact
  obtain ⟨r, t, hrec⟩ := exists_linePowerSections_of_limit D c hc i L n U hU
    hcompact (fun k ↦ (he k).some) s
  let M := (pullback (D.map r.hom)).obj L
  let V (l : T) := sectionGeneratorOpen (tensorPower M n) (t l)
  have hM : LocallyFreeRankOne M := hL.pullback (D.map r.hom)
  have hV (l : T) : IsCompact (V l : Set (D.obj r.left)) :=
    (hM.tensorPower n).isCompact_sectionGeneratorOpen (t l)
  have hpre (l : T) : IsAffineOpen (c.π.app r.left ⁻¹ᵁ V l) := by
    rw [hrec l]
    exact haff l
  have htop : (⨆ l, c.π.app r.left ⁻¹ᵁ V l) = ⊤ := by
    dsimp only [V, M]
    simp_rw [hrec]
    exact hcover
  obtain ⟨j, f, hj, hcov⟩ :=
    exists_affine_cover_preimages_of_finite D c hc r.left V hV hpre htop
  have hB := ampleLineBundle_of_preimage_section_cover hM (D.map f) hn t hcov hj
  refine ⟨j, f ≫ r.hom, ?_⟩
  rw [D.map_comp]
  exact hB.of_iso ((pullbackComp (D.map f) (D.map r.hom)).app L).symm

end FLT.Mazur.Approximation
