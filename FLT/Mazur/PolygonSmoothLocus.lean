/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonAtlasSmoothLocus
public import FLT.Mazur.PolygonSplitGroup

/-!
# The smooth group of a specified polygon pinching

The full Laurent normalization components identify the smooth locus of any
pushout of the specified pinching diagram with the split commutative group.
Local finite presentation is supplied by `polygon_lfp`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
universe u
namespace FLT.Mazur.PolygonPinching
variable (K : Type u) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)

/-- The specified Laurent component, transported through the cocone comparison. -/
@[reassoc]
theorem torus_polygonIso (i : Fin n) :
    PolygonAtlas.torus K n i ≫ (polygonIso K n hn p q h).hom =
      torusToComponent K ≫ componentι K n i ≫ p := by
  simp [PolygonAtlas.torus]

include h in
/-- The punctured normalization components are open immersions in every realization. -/
theorem torus_isOpenImmersion (i : Fin n) :
    IsOpenImmersion (torusToComponent K ≫ componentι K n i ≫ p).left := by
  rw [← torus_polygonIso K n hn p q h]
  have : IsIso (polygonIso K n hn p q h).hom.left :=
    inferInstanceAs (IsIso ((Over.forget _).map (polygonIso K n hn p q h).hom))
  change IsOpenImmersion ((PolygonAtlas.torus K n i).left ≫ _)
  infer_instance

variable [LocallyOfFinitePresentation C.hom]

include h in
/-- The geometric smooth-locus equality transports through the specified comparison. -/
theorem smooth_range : (C.hom.smoothLocus : Set C.left) =
    ⋃ i : Fin n, Set.range (torusToComponent K ≫ componentι K n i ≫ p).left := by
  let e : (PolygonAtlas.polygon K n).left ≅ C.left :=
    (Over.forget _).mapIso (polygonIso K n hn p q h)
  have he (z : (PolygonAtlas.polygon K n).left) :
      e.hom z ∈ C.hom.smoothLocus ↔ z ∈ (PolygonAtlas.polygon K n).hom.smoothLocus := by
    have he := PolygonAtlas.mem_smooth_iff e.hom C.hom z
    simpa only [e, Functor.mapIso_hom, Over.forget_map, Over.w] using he
  ext x
  have hs : Function.Surjective (e.hom : (PolygonAtlas.polygon K n).left → C.left) :=
    e.hom.homeomorph.surjective
  obtain ⟨z, rfl⟩ := hs x
  change e.hom z ∈ C.hom.smoothLocus ↔ _
  rw [he]
  change z ∈ ((PolygonAtlas.polygon K n).hom.smoothLocus : Set _) ↔ _
  rw [PolygonAtlas.smooth_range]
  simp only [Set.mem_iUnion, Set.mem_range]
  constructor
  · rintro ⟨i, y, rfl⟩
    refine ⟨i, y, ?_⟩
    exact congrArg (fun f ↦ f.left y) (torus_polygonIso K n hn p q h i).symm
  · rintro ⟨i, y, hy⟩
    refine ⟨i, y, e.hom.isOpenEmbedding.injective ?_⟩
    exact (congrArg (fun f ↦ f.left y) (torus_polygonIso K n hn p q h i)).trans hy

/-- The smooth open regarded as a scheme over the coefficient field. -/
abbrev smoothPolygon : Over (Spec (.of K)) := Over.mk (C.hom.smoothLocus.ι ≫ C.hom)

/-- The specified component lifted to the smooth locus, indexed by ZMod n. -/
def smoothComponent (i : ZMod n) : MultiplicativeGroupScheme.gm K ⟶ smoothPolygon K (C := C) :=
  Over.homMk (IsOpenImmersion.lift C.hom.smoothLocus.ι
    (torusToComponent K ≫ componentι K n ((ZMod.finEquiv n).symm i) ≫ p).left (by
      change Set.range (torusToComponent K ≫
        componentι K n ((ZMod.finEquiv n).symm i) ≫ p).left ⊆
          Set.range (C.hom.smoothLocus.ι : C.hom.smoothLocus.toScheme ⟶ C.left)
      rw [Scheme.Opens.range_ι, smooth_range K n hn p q h]
      intro x hx
      exact Set.mem_iUnion.mpr ⟨(ZMod.finEquiv n).symm i, hx⟩)) (by
    change IsOpenImmersion.lift _ _ _ ≫ (C.hom.smoothLocus.ι ≫ C.hom) = _
    rw [← Category.assoc, IsOpenImmersion.lift_fac]
    exact (torusToComponent K ≫ componentι K n ((ZMod.finEquiv n).symm i) ≫ p).w)

@[reassoc (attr := simp)]
theorem smoothComponent_ι (i : ZMod n) :
    (smoothComponent K n hn p q h i).left ≫ C.hom.smoothLocus.ι =
      (torusToComponent K ≫ componentι K n ((ZMod.finEquiv n).symm i) ≫ p).left :=
  IsOpenImmersion.lift_fac _ _ _

instance smoothComponent_isOpenImmersion (i : ZMod n) :
    IsOpenImmersion (smoothComponent K n hn p q h i).left := by
  let := torus_isOpenImmersion K n hn p q h ((ZMod.finEquiv n).symm i)
  exact inferInstanceAs (IsOpenImmersion (IsOpenImmersion.lift _ _ _))

/-- The lifted Laurent components cover the smooth open. -/
theorem smoothComponent_cover :
    ⨆ i, (smoothComponent K n hn p q h i).left.opensRange = ⊤ := by
  apply top_unique
  intro x _
  have hx : C.hom.smoothLocus.ι x ∈ (C.hom.smoothLocus : Set _) := x.property
  rw [smooth_range K n hn p q h] at hx
  obtain ⟨i, y, hy⟩ := Set.mem_iUnion.mp hx
  apply TopologicalSpace.Opens.mem_iSup.mpr
  refine ⟨ZMod.finEquiv n i, y, C.hom.smoothLocus.ι.isOpenEmbedding.injective ?_⟩
  have he := congrArg (fun f ↦ f y) (smoothComponent_ι K n hn p q h (ZMod.finEquiv n i))
  simp only [RingEquiv.symm_apply_apply] at he
  exact he.trans hy

/-- Distinct lifted components are disjoint. -/
theorem smoothComponent_disjoint {i j : ZMod n} (hij : i ≠ j) :
    Disjoint (smoothComponent K n hn p q h i).left.opensRange
      (smoothComponent K n hn p q h j).left.opensRange := by
  rw [← TopologicalSpace.Opens.coe_disjoint]
  apply Set.disjoint_left.mpr
  rintro _ ⟨x, rfl⟩ ⟨y, hy⟩
  have he := congrArg (fun z ↦ C.hom.smoothLocus.ι z) hy
  change ((smoothComponent K n hn p q h j).left ≫ C.hom.smoothLocus.ι) y =
    ((smoothComponent K n hn p q h i).left ≫ C.hom.smoothLocus.ι) x at he
  rw [smoothComponent_ι, smoothComponent_ι,
    ← torus_polygonIso K n hn p q h, ← torus_polygonIso K n hn p q h] at he
  have : IsIso (polygonIso K n hn p q h).hom.left :=
    inferInstanceAs (IsIso ((Over.forget _).map (polygonIso K n hn p q h).hom))
  have he' := (polygonIso K n hn p q h).hom.left.isOpenEmbedding.injective he
  exact Set.disjoint_left.mp
    (PolygonAtlas.disjoint_torus K n ((ZMod.finEquiv n).symm.injective.ne hij))
    ⟨x, rfl⟩ ⟨y, he'⟩

/-- The smooth locus is the coproduct of the specified Laurent components over K. -/
def smoothCofanIsColimit : IsColimit (Cofan.mk (smoothPolygon K (C := C))
    (smoothComponent K n hn p q h)) := by
  apply isColimitOfReflects (Over.forget (Spec (.of K)))
  refine (isColimitMapCoconeCofanMkEquiv (Over.forget _) _ _).symm ?_
  exact (nonempty_isColimit_cofanMk_of _
    (smoothComponent_cover K n hn p q h)
    (fun _ _ hij ↦ smoothComponent_disjoint K n hn p q h hij)).some

/-- The smooth locus, with its specified component coordinates, is the split group. -/
def smoothIso : smoothPolygon K (C := C) ≅ PolygonSplitGroup.model K n :=
  (smoothCofanIsColimit K n hn p q h).coconePointUniqueUpToIso (coproductIsCoproduct _)

/-- The inverse isomorphism has exactly the required normalization component formula. -/
@[reassoc]
theorem component_smoothIso_inv (i : Fin n) :
    (Sigma.ι _ (ZMod.finEquiv n i) ≫ (smoothIso K n hn p q h).inv).left ≫
      C.hom.smoothLocus.ι = (torusToComponent K ≫ componentι K n i ≫ p).left := by
  have he : Sigma.ι _ (ZMod.finEquiv n i) ≫ (smoothIso K n hn p q h).inv =
      smoothComponent K n hn p q h (ZMod.finEquiv n i) :=
    (coproductIsCoproduct _).comp_coconePointUniqueUpToIso_hom
      (smoothCofanIsColimit K n hn p q h) ⟨ZMod.finEquiv n i⟩
  rw [he, smoothComponent_ι, RingEquiv.symm_apply_apply]

/-- The group structure transported through the specified smooth-locus isomorphism. -/
abbrev smoothGrpObj : GrpObj (smoothPolygon K (C := C)) :=
  GrpObj.ofIso (smoothIso K n hn p q h).symm

/-- The transported polygon smooth group is commutative. -/
abbrev smoothCommGrpObj : CommGrpObj (smoothPolygon K (C := C)) where
  __ := smoothGrpObj K n hn p q h
  mul_comm := by
    change (β_ _ _).hom ≫
      ((smoothIso K n hn p q h).hom ⊗ₘ (smoothIso K n hn p q h).hom) ≫
        MonObj.mul ≫ (smoothIso K n hn p q h).inv = _
    rw [← BraidedCategory.braiding_naturality_assoc, IsCommMonObj.mul_comm_assoc]
    rfl

end FLT.Mazur.PolygonPinching
