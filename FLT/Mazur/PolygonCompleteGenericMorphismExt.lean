/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteFamilyFlatness
public import FLT.Mazur.PolygonCompleteSmoothCyclicMarking
public import FLT.Mazur.SurjectiveDominantEpi
public import FLT.Mazur.ChowProductOpenGluing

/-!
# Generic fibers detect morphisms on the actual complete family

Flatness makes the generic fiber schematically dense, including on the actual
smooth open and its products. This detects equality of any proposed operations
into the separated complete family; it does not construct those operations.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  (F : Type) [Field F] [Algebra (PowerSeries K) F] [IsFractionRing (PowerSeries K) F]
local notation "S" => Spec (CommRingCat.of (PowerSeries K))
local notation "b" => Spec.map (CommRingCat.ofHom (algebraMap (PowerSeries K) F))
local notation "q" => exactVeroneseProjToBase K n h

/-- Every flat scheme over the original coefficient ring has a schematically dense generic fiber. -/
theorem completeFlat_generic_dense {X : Scheme} (t : X ⟶ S) [Flat t] :
    IsSchemeTheoreticallyDominant (pullback.fst t b) := by
  let _ := SurjectiveDominantEpi.spec_schematic (algebraMap (PowerSeries K) F)
    (IsFractionRing.injective (PowerSeries K) F)
  infer_instance

/-- Generic equality detects actual morphisms into any separated target over the complete base. -/
theorem completeFlat_generic_ext {X Y : Scheme} (t : X ⟶ S) [Flat t]
    (v : Y ⟶ S) [IsSeparated v] (f g : X ⟶ Y) (hb : f ≫ v = g ≫ v)
    (hf : pullback.fst t b ≫ f = pullback.fst t b ≫ g) : f = g := by
  let _ := completeFlat_generic_dense K F t
  exact Chow.schematicallyDense_ext v hb (pullback.fst t b) hf

/-- Generic equality detects maps from flat sources into the original complete total space. -/
theorem completeFlat_toComplete_generic_ext {X : Scheme} (t : X ⟶ S) [Flat t]
    (f g : X ⟶ exactVeroneseProj K n h) (hb : f ≫ q = g ≫ q)
    (hf : pullback.fst t b ≫ f = pullback.fst t b ≫ g) : f = g := by
  let _ := exactVeroneseProjToBase_isProper K n h
  exact completeFlat_generic_ext K F t q f g hb hf

/-- Categorical generic base change is faithful on maps from flat sources to separated targets. -/
theorem completeFlat_generic_map_injective {X Y : Over S} [Flat X.hom] [IsSeparated Y.hom]
    (f g : X ⟶ Y) (hf : (Over.pullback b).map f = (Over.pullback b).map g) : f = g := by
  apply Over.OverMorphism.ext
  apply completeFlat_generic_ext K F X.hom Y.hom f.left g.left (f.w.trans g.w.symm)
  have he := congrArg (fun t ↦ t.left ≫ pullback.fst Y.hom b) hf
  simpa only [Over.pullback_map_left, pullback.lift_fst] using he

attribute [local instance] exactVeroneseProjToBase_lfp
local notation "j" => Scheme.Opens.ι (Scheme.Hom.smoothLocus (exactVeroneseProjToBase K n h))
local notation "G" => Over.mk (j ≫ q)

/-- The actual complete smooth locus is flat over the original coefficient base. -/
theorem completeSmooth_flat : Flat (j ≫ q) := by
  let _ := exactVeroneseProjToBase_flat K n h
  infer_instance

/-- Generic equality detects candidate multiplication maps on the full complete smooth locus. -/
theorem completeSmooth_mul_generic_ext (f g : G ⊗ G ⟶ G)
    (hf : pullback.fst (G ⊗ G).hom b ≫ f.left =
      pullback.fst (G ⊗ G).hom b ≫ g.left) : f = g := by
  let _ := completeSmooth_flat K n h
  let _ := exactVeroneseProjToBase_isProper K n h
  let _ : Flat (G ⊗ G).hom := by
    change Flat (pullback.fst (j ≫ q) (j ≫ q) ≫ (j ≫ q))
    infer_instance
  apply Over.OverMorphism.ext
  apply completeFlat_generic_ext K F (G ⊗ G).hom (j ≫ q) f.left g.left
  · exact f.w.trans g.w.symm
  · exact hf

/-- Generic equality detects candidate whole-curve actions by the complete smooth locus. -/
theorem completeSmooth_action_generic_ext (f g : G ⊗ Over.mk q ⟶ Over.mk q)
    (hf : pullback.fst (G ⊗ Over.mk q).hom b ≫ f.left =
      pullback.fst (G ⊗ Over.mk q).hom b ≫ g.left) : f = g := by
  let _ := completeSmooth_flat K n h
  let _ := exactVeroneseProjToBase_flat K n h
  let _ : Flat (G ⊗ Over.mk q).hom := by
    change Flat (pullback.fst (j ≫ q) q ≫ (j ≫ q))
    infer_instance
  apply Over.OverMorphism.ext
  exact completeFlat_toComplete_generic_ext K n h F (G ⊗ Over.mk q).hom f.left g.left
    (f.w.trans g.w.symm) hf

end FLT.Mazur.PolygonInfinitesimalStages
