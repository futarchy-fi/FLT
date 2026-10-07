/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicVariableChangeOverlap

/-! # Global Weierstrass coordinate changes over arbitrary coefficient rings -/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false

namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (C : VariableChange R)

/-- The two principal opens refining the infinity chart for the coordinate change. -/
def variableChangeInfinityOpen (b : Bool) : Scheme.{u} :=
  if b then Spec (.of (VariableChangeNeighborhood W C)) else Spec (.of (Overlap (C • W) true))

/-- Inclusion of each principal open into the infinity chart. -/
def variableChangeInfinityInclusion (b : Bool) :
    variableChangeInfinityOpen W C b ⟶ chart (C • W) true := by
  cases b
  · exact overlapInclusion (C • W) true
  · exact Spec.map (CommRingCat.ofHom
      (algebraMap (Ring (C • W) true) (VariableChangeNeighborhood W C)))

instance variableChangeInfinityInclusion_isOpenImmersion (b : Bool) :
    IsOpenImmersion (variableChangeInfinityInclusion W C b) := by
  cases b
  · exact overlapInclusion_isOpenImmersion (C • W) true
  · exact IsOpenImmersion.of_isLocalization (variableChangeInfinityDenominator W C)

/-- The ordinary overlap and the coordinate-change neighborhood cover the infinity chart. -/
def variableChangeInfinityCover : (chart (C • W) true).OpenCover where
  I₀ := Bool
  X := variableChangeInfinityOpen W C
  f := variableChangeInfinityInclusion W C
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_, inferInstance⟩
    intro x
    by_cases hv : coord (C • W) true 1 ∈ x.asIdeal
    · have hd : variableChangeInfinityDenominator W C ∉ x.asIdeal := by
        intro hd
        apply x.isPrime.ne_top
        apply top_unique
        rw [← variableChange_infinity_span W C]
        apply Ideal.span_le.mpr
        rintro y (rfl | hy)
        · exact hv
        · rcases Set.mem_singleton_iff.mp hy with rfl
          exact hd
      have hr := PrimeSpectrum.localization_away_comap_range (VariableChangeNeighborhood W C)
        (variableChangeInfinityDenominator W C)
      obtain ⟨y, hy⟩ := (Set.ext_iff.mp hr x).mpr hd
      exact ⟨true, y, hy⟩
    · obtain ⟨y, hy⟩ := (Set.ext_iff.mp (overlapInclusion_range (C • W) true) x).mpr hv
      exact ⟨false, y, hy⟩

/-- The two local coordinate changes on the refined infinity cover. -/
def variableChangeInfinityPiece (b : Bool) : variableChangeInfinityOpen W C b ⟶ scheme W := by
  cases b
  · exact Spec.map (CommRingCat.ofHom (changeChart (C • W) true).toRingHom) ≫
      variableChangeAffineMorphism W C ≫ affineChart W
  · exact variableChangeInfinityMorphism W C ≫ infinityChart W

theorem variableChangeInfinityPiece_agreement :
    pullback.fst (variableChangeInfinityInclusion W C false)
        (variableChangeInfinityInclusion W C true) ≫
        variableChangeInfinityPiece W C false =
      pullback.snd _ _ ≫ variableChangeInfinityPiece W C true := by
  let e := (variableChange_refined_isPullback W C).isoPullback
  apply (cancel_epi e.hom).mp
  change e.hom ≫ pullback.fst _ _ ≫
      (Spec.map (CommRingCat.ofHom (changeChart (C • W) true).toRingHom) ≫
        variableChangeAffineMorphism W C ≫ affineChart W) =
    e.hom ≫ pullback.snd _ _ ≫ (variableChangeInfinityMorphism W C ≫ infinityChart W)
  simp only [e, IsPullback.isoPullback_hom_fst_assoc, IsPullback.isoPullback_hom_snd_assoc]
  rw [← Category.assoc, ← Spec.map_comp]
  exact variableChange_refined_overlap_agreement W C

theorem variableChangeInfinityPiece_gluing (b c : Bool) :
    pullback.fst (variableChangeInfinityInclusion W C b) (variableChangeInfinityInclusion W C c) ≫
        variableChangeInfinityPiece W C b =
      pullback.snd _ _ ≫ variableChangeInfinityPiece W C c := by
  cases b <;> cases c
  · have h : pullback.fst (variableChangeInfinityInclusion W C false)
          (variableChangeInfinityInclusion W C false) =
        pullback.snd _ _ :=
      (cancel_mono (variableChangeInfinityInclusion W C false)).mp pullback.condition
    rw [h]
  · exact variableChangeInfinityPiece_agreement W C
  · apply (cancel_epi
      (pullbackSymmetry (variableChangeInfinityInclusion W C false)
        (variableChangeInfinityInclusion W C true)).hom).mp
    simpa only [pullbackSymmetry_hom_comp_fst_assoc, pullbackSymmetry_hom_comp_snd_assoc] using
      (variableChangeInfinityPiece_agreement W C).symm
  · have h : pullback.fst (variableChangeInfinityInclusion W C true)
          (variableChangeInfinityInclusion W C true) =
        pullback.snd _ _ :=
      (cancel_mono (variableChangeInfinityInclusion W C true)).mp pullback.condition
    rw [h]

/-- The coordinate change on the whole infinity chart, obtained by gluing its refined cover. -/
def variableChangeInfinityGlued : chart (C • W) true ⟶ scheme W :=
  (variableChangeInfinityCover W C).glueMorphisms (variableChangeInfinityPiece W C)
    (variableChangeInfinityPiece_gluing W C)

@[reassoc (attr := simp)] theorem overlap_variableChangeInfinityGlued :
    overlapInclusion (C • W) true ≫ variableChangeInfinityGlued W C =
      Spec.map (CommRingCat.ofHom (changeChart (C • W) true).toRingHom) ≫
        variableChangeAffineMorphism W C ≫ affineChart W :=
  (variableChangeInfinityCover W C).ι_glueMorphisms _ _ false

@[reassoc (attr := simp)] theorem neighborhood_variableChangeInfinityGlued :
    Spec.map (CommRingCat.ofHom (algebraMap (Ring (C • W) true) (VariableChangeNeighborhood W C))) ≫
        variableChangeInfinityGlued W C = variableChangeInfinityMorphism W C ≫ infinityChart W :=
  (variableChangeInfinityCover W C).ι_glueMorphisms _ _ true

theorem variableChange_gluing :
    overlapInclusion (C • W) false ≫ (variableChangeAffineMorphism W C ≫ affineChart W) =
      overlapRight (C • W) ≫ variableChangeInfinityGlued W C := by
  have hc : (overlapIso (C • W)).hom ≫
      Spec.map (CommRingCat.ofHom (changeChart (C • W) true).toRingHom) =
        overlapInclusion (C • W) false := by
    apply (cancel_mono (affineChart (C • W))).mp
    rw [Category.assoc, changeChart_true_to_scheme]
    exact (overlap_condition (C • W)).symm
  unfold overlapRight
  rw [Category.assoc, overlap_variableChangeInfinityGlued]
  simpa only [Category.assoc] using
    (congrArg (fun f ↦ f ≫ variableChangeAffineMorphism W C ≫ affineChart W) hc).symm

/-- The coordinate change on the glued Weierstrass cubic over an arbitrary commutative base. -/
def variableChangeMorphism : scheme (C • W) ⟶ scheme W :=
  pushout.desc (variableChangeAffineMorphism W C ≫ affineChart W) (variableChangeInfinityGlued W C)
    (variableChange_gluing W C)

@[reassoc (attr := simp)] theorem affineChart_variableChange :
    affineChart (C • W) ≫ variableChangeMorphism W C =
      variableChangeAffineMorphism W C ≫ affineChart W :=
  pushout.inl_desc _ _ _

@[reassoc (attr := simp)] theorem infinityChart_variableChange :
    infinityChart (C • W) ≫ variableChangeMorphism W C = variableChangeInfinityGlued W C :=
  pushout.inr_desc _ _ _

theorem variableChange_overlap_toBase :
    overlapInclusion (C • W) true ≫ (variableChangeInfinityGlued W C ≫ toBase W) =
      overlapInclusion (C • W) true ≫ chartToBase (C • W) true := by
  rw [overlap_variableChangeInfinityGlued_assoc]
  simp only [affineChart_toBase, variableChangeAffineMorphism_toBase]
  have h := congrArg (fun f => f ≫ toBase (C • W))
    (changeChart_true_to_scheme (C • W))
  simpa only [Category.assoc, affineChart_toBase, infinityChart_toBase] using h

private theorem specAlgHom_toBase {A B : Type u} [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (f : A →ₐ[R] B) :
    Spec.map (CommRingCat.ofHom f.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R A)) =
      Spec.map (CommRingCat.ofHom (algebraMap R B)) := by
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  exact RingHom.ext f.commutes

theorem variableChange_neighborhood_toBase :
    Spec.map (CommRingCat.ofHom
      (algebraMap (Ring (C • W) true) (VariableChangeNeighborhood W C))) ≫
        (variableChangeInfinityGlued W C ≫ toBase W) =
      Spec.map (CommRingCat.ofHom
        (algebraMap (Ring (C • W) true) (VariableChangeNeighborhood W C))) ≫
          chartToBase (C • W) true := by
  rw [neighborhood_variableChangeInfinityGlued_assoc]
  simp only [infinityChart_toBase]
  exact (specAlgHom_toBase (variableChangeInfinityMap W C)).trans
    (specAlgHom_toBase
      (IsScalarTower.toAlgHom R (Ring (C • W) true) (VariableChangeNeighborhood W C))).symm


@[reassoc] theorem variableChangeInfinityGlued_toBase :
    variableChangeInfinityGlued W C ≫ toBase W = chartToBase (C • W) true := by
  apply (variableChangeInfinityCover W C).hom_ext
  intro b
  cases b
  · exact variableChange_overlap_toBase W C
  · exact variableChange_neighborhood_toBase W C

/-- The globally glued coordinate change is a morphism over the coefficient base. -/
@[reassoc (attr := simp)] theorem variableChange_toBase :
    variableChangeMorphism W C ≫ toBase W = toBase (C • W) := by
  apply pushout.hom_ext
  · change affineChart (C • W) ≫ (variableChangeMorphism W C ≫ toBase W) =
      affineChart (C • W) ≫ toBase (C • W)
    simp only [affineChart_variableChange_assoc, affineChart_toBase,
      variableChangeAffineMorphism_toBase]
  · change infinityChart (C • W) ≫ (variableChangeMorphism W C ≫ toBase W) =
      infinityChart (C • W) ≫ toBase (C • W)
    simp only [infinityChart_variableChange_assoc, infinityChart_toBase,
      variableChangeInfinityGlued_toBase]

end WeierstrassCurve.CubicCharts
