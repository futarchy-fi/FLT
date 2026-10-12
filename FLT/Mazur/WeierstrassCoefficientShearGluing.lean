/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearAtlasStructure
public import Mathlib.AlgebraicGeometry.Gluing

/-!
# Gluing the complete sheared coefficient equations

Glue every full equation along its actual full scheme intersections. The resulting
scheme is the original coefficient pullback, retaining both projections and the cubic map.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [CommRing S] [Algebra R S] (r : S) (t : ℕ) (ht : t ≤ n)
/-- The same finite equation cover with indices lifted to the scheme universe for gluing. -/
def coefficientShearGluingCover :
    Scheme.OpenCover.{u} (finiteGlobalTensorModel hπ data S t ht) where
  I₀ := ULift.{u} (Fin 3 ⊕ Fin t)
  X i := coefficientShearAtlasObject data S r t ht i.down
  f i := coefficientShearAtlasMap hπ data S r t ht i.down
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_, fun i => coefficientShearAtlasMap_isOpenImmersion hπ data S r t ht i.down⟩
    intro z
    obtain ⟨i, x, hx⟩ := coefficientShearAtlas_cover hπ data S r t ht z
    exact ⟨⟨i⟩, x, hx⟩

local notation "C" => coefficientShearGluingCover hπ data S r t ht
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R S))

/-- The gluing of the actual full sheared equations and the original infinity tensor chart. -/
def coefficientShearGlued : Scheme := (C).gluedCover.glued

/-- The complete equation gluing identifies the entire original coefficient pullback. -/
def coefficientShearGluedIso :
    coefficientShearGlued hπ data S r t ht ≅ finiteGlobalTensorModel hπ data S t ht :=
  asIso (C).fromGlued

/-- Inclusion of each full equation into its glued model. -/
def coefficientShearGluedChart (i : Fin 3 ⊕ Fin t) :
    coefficientShearAtlasObject data S r t ht i ⟶ coefficientShearGlued hπ data S r t ht :=
  (C).gluedCover.ι ⟨i⟩

instance coefficientShearGluedChart_isOpenImmersion (i : Fin 3 ⊕ Fin t) :
    IsOpenImmersion (coefficientShearGluedChart hπ data S r t ht i) :=
  inferInstanceAs (IsOpenImmersion ((C).gluedCover.ι ⟨i⟩))

/-- Reconstruction retains the actual full chart morphisms into the original pullback. -/
@[reassoc] theorem coefficientShearGluedIso_chart (i : Fin 3 ⊕ Fin t) :
    coefficientShearGluedChart hπ data S r t ht i ≫
        (coefficientShearGluedIso hπ data S r t ht).hom =
      coefficientShearAtlasMap hπ data S r t ht i :=
  (C).ι_fromGlued ⟨i⟩

/-- The glued equations have their ordinary extended coefficient structure. -/
def coefficientShearGluedStructure :=
  (coefficientShearGluedIso hπ data S r t ht).hom ≫
    pullback.fst q (finiteGlobalStructure hπ data t ht)

/-- The comparison retains the projection to the whole original integral finite model. -/
def coefficientShearGluedProjection :=
  (coefficientShearGluedIso hπ data S r t ht).hom ≫
    pullback.snd q (finiteGlobalStructure hπ data t ht)

/-- The actual coefficient maps of all equations glue to the constructed structure morphism. -/
@[reassoc] theorem coefficientShearGluedChart_structure (i : Fin 3 ⊕ Fin t) :
    coefficientShearGluedChart hπ data S r t ht i ≫
        coefficientShearGluedStructure hπ data S r t ht =
      coefficientShearAtlasStructure data S r t ht i := by
  rw [coefficientShearGluedStructure, coefficientShearGluedIso_chart_assoc,
    coefficientShearAtlasMap_structure]

/-- Every original function of the integral finite model survives the glued comparison. -/
@[reassoc] theorem coefficientShearGluedChart_projection (i : Fin 3 ⊕ Fin t) :
    coefficientShearGluedChart hπ data S r t ht i ≫
        coefficientShearGluedProjection hπ data S r t ht =
      coefficientShearAtlasMap hπ data S r t ht i ≫
        pullback.snd q (finiteGlobalStructure hπ data t ht) := by
  rw [coefficientShearGluedProjection, coefficientShearGluedIso_chart_assoc]

/-- The glued coefficient and integral projections form the original cartesian square. -/
theorem coefficientShearGlued_isPullback :
    IsPullback (coefficientShearGluedStructure hπ data S r t ht)
      (coefficientShearGluedProjection hπ data S r t ht) q
      (finiteGlobalStructure hπ data t ht) := by
  exact (IsPullback.of_hasPullback q (finiteGlobalStructure hπ data t ht)).of_iso
    (coefficientShearGluedIso hπ data S r t ht).symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp [coefficientShearGluedStructure])
    (by simp [coefficientShearGluedProjection]) (by simp) (by simp)

end FLT.Mazur.WeierstrassDividedDepth
