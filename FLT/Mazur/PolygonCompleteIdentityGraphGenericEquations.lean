/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityGraphSmoothEquations

/-!
# Generic smooth-graph equations before adic specialization

Flatness of the original smooth input makes its generic fiber schematically
dense. Thus generic smooth-graph equations generate exactly the full original
graph ideal, which is then pulled back to each actual adic chart.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "V" => completeIdentityActionSmoothOpen K n h
local notation "f" => completeIdentityActionSmoothGraph K n h
local notation "s" => completeIdentityActionSecond K n h
local notation "π" => exactVeroneseProjToBase K n h
local notation "b" => Spec.map
  (CommRingCat.ofHom (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))))

/-- The generic fiber of the original domain of the constructed smooth action. -/
abbrev completeIdentityActionGenericSmoothInput : Scheme := pullback ((V).ι ≫ (s) ≫ (π)) (b)

/-- The original generic smooth input maps to the original complete smooth input. -/
abbrev completeIdentityActionGenericSmoothInclusion :=
  pullback.fst ((V).ι ≫ (s) ≫ (π)) (b)
local notation "u" => completeIdentityActionGenericSmoothInclusion K n h

/-- Generic density is used before any nilpotent base change. -/
instance completeIdentityActionGenericSmooth_schematic : IsSchemeTheoreticallyDominant (u) :=
  completeFlat_generic_dense K (FractionRing (PowerSeries K)) ((V).ι ≫ (s) ≫ (π))

instance completeIdentityActionGenericSmooth_quasiCompact : QuasiCompact (u) := inferInstance

/-- The actual generic smooth graph, still mapped into the original complete lifting space. -/
def completeIdentityActionGenericSmoothGraph :
    completeIdentityActionGenericSmoothInput K n h ⟶ completeIdentityActionLiftSpace K n h :=
  (u) ≫ (f)
local notation "g" => completeIdentityActionGenericSmoothGraph K n h

instance completeIdentityActionGenericSmoothGraph_quasiCompact : QuasiCompact (g) := by
  unfold completeIdentityActionGenericSmoothGraph
  infer_instance

/-- The generic graph has exactly the full original smooth graph kernel. -/
theorem completeIdentityActionGenericSmoothGraph_kernel : (g).ker = (f).ker := by
  rw [completeIdentityActionGenericSmoothGraph, Scheme.Hom.ker_comp, Scheme.Hom.ker_eq_bot,
    Scheme.IdealSheafData.map_bot]

/-- The original smooth-graph section kernel can be computed on its generic fiber. -/
theorem completeIdentityActionSmoothGraph_affineKernel
    (W : (completeIdentityActionLiftSpace K n h).affineOpens) :
    RingHom.ker ((f).app W).hom = RingHom.ker ((g).app W).hom := by
  rw [← Scheme.Hom.ker_apply, ← Scheme.Hom.ker_apply,
    completeIdentityActionGenericSmoothGraph_kernel]

/-- Generic equations are pulled back only after forming their full original kernel. -/
theorem completeIdentityActionGraphAdicChart_genericIdeal (m : ℕ) (i j : Fin n) :
    (g).ker.comap (completeIdentityActionAdicChartSpaceMap K n h m i j ≫
      completeIdentityActionAdicLiftSpaceMap K n h m) =
      (completeIdentityActionGraphAdicChartEmbedding K n h m i j).ker := by
  rw [completeIdentityActionGenericSmoothGraph_kernel,
    completeIdentityActionGraphAdicChart_smoothIdeal]

attribute [local irreducible] completeIdentityActionAdicChartSpaceMap
  completeIdentityActionAdicLiftSpaceMap completeIdentityActionGenericSmoothGraph
variable (m : ℕ) (i j : Fin n)
local notation "R" => completeIdentityActionAdicChartSpace K n h m i j
local notation "k" => completeIdentityActionAdicChartSpaceMap K n h m i j ≫
  completeIdentityActionAdicLiftSpaceMap K n h m
local notation "c" => completeIdentityActionGraphAdicChartEmbedding K n h m i j

/-- On any compatible affine pair, the generic kernel generates exactly the full chart ideal. -/
theorem completeIdentityActionGraphAdicChart_localGenericEquations
    (W : (completeIdentityActionLiftSpace K n h).affineOpens)
    (U : (R).affineOpens) (e : U.1 ≤ (k) ⁻¹ᵁ W.1) :
    (c).ker.ideal U = (RingHom.ker ((g).app W).hom).map ((k).appLE W U e).hom := by
  rw [completeIdentityActionGraphAdicChart_localEquations K n h m i j W U e,
    completeIdentityActionSmoothGraph_affineKernel]

/-- Every actual ambient point has such an affine equation patch; no single chart is assumed. -/
theorem completeIdentityActionGraphAdicChart_exists_genericEquationPatch (x : R) :
    ∃ (W : (completeIdentityActionLiftSpace K n h).affineOpens)
      (U : (R).affineOpens) (e : U.1 ≤ (k) ⁻¹ᵁ W.1), x ∈ U.1 ∧
        (c).ker.ideal U = (RingHom.ker ((g).app W).hom).map ((k).appLE W U e).hom := by
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, _⟩ :=
    (completeIdentityActionLiftSpace K n h).isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ ((k) x)) TopologicalSpace.isOpen_univ
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUW⟩ :=
    (R).isBasis_affineOpens.exists_subset_of_mem_open hxW ((k) ⁻¹ᵁ W).isOpen
  exact ⟨⟨W, hW⟩, ⟨U, hU⟩, hUW, hxU,
    completeIdentityActionGraphAdicChart_localGenericEquations K n h m i j _ _ hUW⟩

end FLT.Mazur.PolygonInfinitesimalStages
