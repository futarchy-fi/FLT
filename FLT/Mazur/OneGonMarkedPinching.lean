/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.ProjectiveLineMobius
public import FLT.Mazur.NeronPolygonPredicate

/-! # The one-gon with the specified zero and infinity marking -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial
open FLT.Mazur.OneGonNormalization FLT.Mazur.OneGonLocalFactorization

namespace FLT.Mazur.OneGonMarkedPinching

universe u
variable (K : Type u) [Field K]

/-- The projective normalization with branches at the specified zero and infinity. -/
def normalization : ProjectiveLine.scheme K ⟶ OneGonGluing.scheme K :=
  ProjectiveLineMobius.map K ≫ projectiveToOneGon K

@[reassoc]
theorem zero_normalization :
    ProjectiveLine.zero K ≫ normalization K =
      ProjectiveLine.zero K ≫ projectiveToOneGon K := by
  rw [normalization, ProjectiveLineMobius.zero_map_assoc]

@[reassoc]
theorem infinity_normalization :
    ProjectiveLine.infinity K ≫ normalization K =
      ProjectiveLine.zero K ≫ projectiveToOneGon K := by
  rw [normalization, ProjectiveLineMobius.infinity_map_assoc]
  exact (endpoints_projectiveToOneGon K).symm

/-- The pinching universal property for the exact zero and infinity sections. -/
theorem existsUnique_desc {T : Scheme.{u}} (f : ProjectiveLine.scheme K ⟶ T)
    (hf : ProjectiveLine.zero K ≫ f = ProjectiveLine.infinity K ≫ f) :
    ∃! d : OneGonGluing.scheme K ⟶ T, normalization K ≫ d = f := by
  have hh : endpointSection 0 ≫ ProjectiveLine.left K ≫ (ProjectiveLineMobius.map K ≫ f) =
      endpointSection 1 ≫ ProjectiveLine.left K ≫ (ProjectiveLineMobius.map K ≫ f) := by
    rw [ProjectiveLineMobius.one_map_assoc]
    change ProjectiveLine.zero K ≫ ProjectiveLineMobius.map K ≫ f = _
    rw [ProjectiveLineMobius.zero_map_assoc]
    exact hf
  obtain ⟨d, hd, hu⟩ := existsUnique_projective_desc K (ProjectiveLineMobius.map K ≫ f) hh
  refine ⟨d, ?_, ?_⟩
  · change normalization K ≫ d = f
    rw [normalization, Category.assoc, hd, ← Category.assoc,
      ProjectiveLineMobius.map_square, Category.id_comp]
  · intro e he
    apply hu
    have h := congrArg (fun m ↦ ProjectiveLineMobius.map K ≫ m) he
    simpa only [normalization, ← Category.assoc, ProjectiveLineMobius.map_square,
      Category.id_comp] using h

/-- Maps from the one-gon are determined by their pullback to the marked normalization. -/
theorem hom_ext {T : Scheme.{u}} (f g : OneGonGluing.scheme K ⟶ T)
    (h : normalization K ≫ f = normalization K ≫ g) : f = g := by
  have he : ProjectiveLine.zero K ≫ (normalization K ≫ g) =
      ProjectiveLine.infinity K ≫ (normalization K ≫ g) := by
    rw [zero_normalization_assoc, infinity_normalization_assoc]
  obtain ⟨d, _, hu⟩ := existsUnique_desc K (normalization K ≫ g) he
  exact (hu f h).trans (hu g rfl).symm

theorem pinching_toBase :
    OneGonPinchingAlgebra.toPinching ≫ PolygonNodePresentation.bToBase K =
      ProjectiveLine.chartToBase K := by
  rw [OneGonPinchingAlgebra.toPinching, PolygonNodePresentation.bToBase,
    ProjectiveLine.chartToBase, ← Spec.map_comp]
  rfl

theorem overlapLeft_toBase :
    ProjectiveLine.overlapLeft K ≫ ProjectiveLine.chartToBase K =
      OneGonGluing.torusToBase K := by
  rw [ProjectiveLine.overlapLeft, ProjectiveLine.chartToBase,
    OneGonGluing.torusToBase, ← Spec.map_comp]
  congr 1
  ext r
  simp

theorem projectiveToOneGon_toBase :
    projectiveToOneGon K ≫ OneGonGluing.toBase K = ProjectiveLine.toBase K := by
  apply (cancel_epi (toProjective K)).mp
  apply pushout.hom_ext
  · change line K ≫ _ = line K ≫ _
    simp only [line_toProjective_assoc, left_projectiveToOneGon_assoc,
      OneGonGluing.node_toBase, ProjectiveLine.left_toBase]
    exact pinching_toBase K
  · change torus K ≫ _ = torus K ≫ _
    simp only [torus_toProjective_assoc, torus_projectiveToOneGon_assoc,
      OneGonGluing.torus_toBase, ProjectiveLine.right_toBase]
    rw [torusToRight, Category.assoc, ProjectiveLineMobius.reflection_toBase,
      ← ProjectiveLine.overlap_toBase, overlapLeft_toBase]

@[reassoc]
theorem normalization_toBase :
    normalization K ≫ OneGonGluing.toBase K = ProjectiveLine.toBase K := by
  rw [normalization, Category.assoc, projectiveToOneGon_toBase, ProjectiveLineMobius.map_toBase]

/-- The constructed one-gon over the original coefficient field. -/
abbrev object : Over (Spec (.of K)) := Over.mk (OneGonGluing.toBase K)

/-- The marked normalization as a morphism over the base. -/
def normalizationOver : PolygonPinching.component K ⟶ object K :=
  Over.homMk (normalization K) (normalization_toBase K)

/-- The node section, obtained from the zero branch. -/
def nodeOver : PolygonPinching.point K ⟶ object K :=
  ProjectiveLine.zeroSection K ≫ normalizationOver K

@[reassoc]
theorem infinity_normalizationOver :
    ProjectiveLine.infinitySection K ≫ normalizationOver K = nodeOver K := by
  apply Over.OverMorphism.ext
  exact (infinity_normalization K).trans (zero_normalization K).symm

/-- Descent with the prescribed marking also holds in schemes over the base. -/
theorem existsUnique_descOver (T : Over (Spec (.of K))) (f : PolygonPinching.component K ⟶ T)
    (hf : ProjectiveLine.zeroSection K ≫ f = ProjectiveLine.infinitySection K ≫ f) :
    ∃! d : object K ⟶ T, normalizationOver K ≫ d = f := by
  have hh : ProjectiveLine.zero K ≫ f.left = ProjectiveLine.infinity K ≫ f.left :=
    congrArg (fun m ↦ m.left) hf
  obtain ⟨d, hd, hu⟩ := existsUnique_desc K f.left hh
  have hb : d ≫ T.hom = OneGonGluing.toBase K := by
    apply hom_ext K
    rw [← Category.assoc, hd, f.w, normalization_toBase]
    rfl
  refine ⟨Over.homMk d hb, ?_, ?_⟩
  · apply Over.OverMorphism.ext
    exact hd
  · intro e he
    apply Over.OverMorphism.ext
    exact hu e.left (congrArg (fun m ↦ m.left) he)

/-- The actual normalization leg of the one-component cyclic diagram. -/
def componentsMap : PolygonPinching.components K 1 ⟶ object K :=
  Sigma.desc fun _ ↦ normalizationOver K

/-- The actual node leg of the one-component cyclic diagram. -/
def nodesMap : PolygonPinching.nodes K 1 ⟶ object K :=
  Sigma.desc fun _ ↦ nodeOver K

@[reassoc (attr := simp)]
theorem component_componentsMap (i : Fin 1) :
    PolygonPinching.componentι K 1 i ≫ componentsMap K = normalizationOver K :=
  Sigma.ι_comp_desc _ _

@[reassoc (attr := simp)]
theorem node_nodesMap (i : Fin 1) :
    PolygonPinching.nodeι K 1 i ≫ nodesMap K = nodeOver K :=
  Sigma.ι_comp_desc _ _

theorem span_commutes (hn : 0 < 1) :
    PolygonPinching.toComponents K 1 hn ≫ componentsMap K =
      PolygonPinching.toNodes K 1 ≫ nodesMap K := by
  apply Sigma.hom_ext
  intro ib
  rcases ib with ⟨i, b⟩
  cases b
  · change PolygonPinching.branchι K 1 i false ≫ _ = PolygonPinching.branchι K 1 i false ≫ _
    simp only [PolygonPinching.branchι_toComponents_zero_assoc,
      PolygonPinching.branchι_toNodes_assoc, component_componentsMap, node_nodesMap]
    rfl
  · change PolygonPinching.branchι K 1 i true ≫ _ = PolygonPinching.branchι K 1 i true ≫ _
    simp only [PolygonPinching.branchι_toComponents_infinity_assoc,
      PolygonPinching.branchι_toNodes_assoc, component_componentsMap, node_nodesMap,
      infinity_normalizationOver]


/-- The constructed one-gon realizes the exact one-component cyclic pinching span over K. -/
theorem isPushout (hn : 0 < 1) :
    IsPushout (PolygonPinching.toComponents K 1 hn) (PolygonPinching.toNodes K 1)
      (componentsMap K) (nodesMap K) := by
  refine ⟨⟨span_commutes K hn⟩, ⟨?_⟩⟩
  apply PushoutCocone.isColimitAux'
  intro s
  let f := PolygonPinching.componentι K 1 0 ≫ s.inl
  let g := PolygonPinching.nodeι K 1 0 ≫ s.inr
  have hz : ProjectiveLine.zeroSection K ≫ f = g := by
    have h := congrArg (fun m ↦ PolygonPinching.branchι K 1 0 false ≫ m) s.condition
    simpa only [PolygonPinching.branchι_toComponents_zero_assoc,
      PolygonPinching.branchι_toNodes_assoc, Category.assoc] using h
  have hi : ProjectiveLine.infinitySection K ≫ f = g := by
    have h := congrArg (fun m ↦ PolygonPinching.branchι K 1 0 true ≫ m) s.condition
    simpa only [PolygonPinching.branchι_toComponents_infinity_assoc,
      PolygonPinching.branchι_toNodes_assoc, PolygonPinching.next_one, Category.assoc] using h
  let hex := existsUnique_descOver K s.pt f (hz.trans hi.symm)
  let d := hex.choose
  have hd : normalizationOver K ≫ d = f := hex.choose_spec.1
  have hu : ∀ e, normalizationOver K ≫ e = f → e = d := hex.choose_spec.2
  have hdn : nodeOver K ≫ d = g := by
    rw [nodeOver, Category.assoc, hd]
    exact hz
  refine ⟨d, ?_, ?_, ?_⟩
  · apply Sigma.hom_ext
    intro i
    have he : i = (0 : Fin 1) := Subsingleton.elim _ _
    subst i
    change PolygonPinching.componentι K 1 0 ≫ (componentsMap K ≫ d) =
      PolygonPinching.componentι K 1 0 ≫ s.inl
    rw [component_componentsMap_assoc]
    exact hd
  · apply Sigma.hom_ext
    intro i
    have he : i = (0 : Fin 1) := Subsingleton.elim _ _
    subst i
    change PolygonPinching.nodeι K 1 0 ≫ (nodesMap K ≫ d) =
      PolygonPinching.nodeι K 1 0 ≫ s.inr
    rw [node_nodesMap_assoc]
    exact hdn
  · intro m hm _
    apply hu
    have h := congrArg (fun e ↦ PolygonPinching.componentι K 1 0 ≫ e) hm
    change PolygonPinching.componentι K 1 0 ≫ componentsMap K ≫ m = f at h
    simpa only [component_componentsMap_assoc] using h

/-- The glued one-gon satisfies the project's specified Néron one-gon predicate. -/
theorem isNeronOneGon (hn : 0 < 1) : IsNeronNGon (object K) 1 hn :=
  ⟨componentsMap K, nodesMap K, isPushout K hn⟩

/-- In particular the constructed scheme is a Néron polygon over K. -/
theorem isNeronPolygon : IsNeronPolygon (object K) :=
  (isNeronOneGon K (by decide)).isNeronPolygon

end FLT.Mazur.OneGonMarkedPinching
