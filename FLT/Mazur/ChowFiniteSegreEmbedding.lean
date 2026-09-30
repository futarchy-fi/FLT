/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ChowGraphEmbedding
public import FLT.Mazur.ChowGraphProductComparison
public import FLT.Mazur.ProjectiveSpaceReindex

/-!
# The finite Segre embedding of the Chow modification

Iterating the binary Segre map embeds the actual finite relative product in
one projective space. The empty product uses the coefficient spectrum as
projective zero-space. Composing with the graph's product immersion gives
an immersion of the modification, which is closed when the source is proper.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

set_option backward.isDefEq.respectTransparency false

namespace FLT.Mazur.ProjectiveSpace

variable (R : Type u) [CommRing R]

/-- The only standard open of projective zero-space is the whole scheme. -/
lemma zeroSpace_chart_eq_top : chart R (Fin 1) 0 = ⊤ := by
  simpa only [iSup_unique, Fin.default_eq_zero] using iSup_chart R (Fin 1)

/-- Affine zero-space covers projective zero-space. -/
instance affineChartEmbedding_zero_isIso : IsIso (affineChartEmbedding R 0) :=
  isIso_of_isOpenImmersion_of_opensRange_eq_top _
    ((affineChartEmbedding_opensRange R 0).trans (zeroSpace_chart_eq_top R))

/-- Polynomial evaluation and the unique chart identify the base with zero-space. -/
def zeroSpaceIso : Spec (.of R) ≅ space R (Fin 1) :=
  Scheme.Spec.mapIso (MvPolynomial.isEmptyRingEquiv R (Fin 0)).toCommRingCatIso.op ≪≫
    asIso (affineChartEmbedding R 0)

@[reassoc (attr := simp)]
lemma zeroSpaceIso_baseProjection :
    (zeroSpaceIso R).hom ≫ baseProjection R (Fin 1) = 𝟙 _ := by
  rw [zeroSpaceIso, Iso.trans_hom, Category.assoc, asIso_hom,
    affineChartEmbedding_baseProjection]
  change Spec.map (CommRingCat.ofHom
    (MvPolynomial.isEmptyRingEquiv R (Fin 0)).toRingHom) ≫
      Spec.map (CommRingCat.ofHom MvPolynomial.C) = _
  rw [← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom
    ((MvPolynomial.isEmptyRingEquiv R (Fin 0)).toRingHom.comp MvPolynomial.C)) = _
  have h : (MvPolynomial.isEmptyRingEquiv R (Fin 0)).toRingHom.comp MvPolynomial.C =
      RingHom.id R := by
    ext r
    exact (MvPolynomial.isEmptyRingEquiv R (Fin 0)).apply_symm_apply r
  rw [h]
  exact Scheme.Spec.map_id _

end FLT.Mazur.ProjectiveSpace

namespace FLT.Mazur.Chow

open ProjectiveSpace

variable (k : Type u) [Field k]

/-- The same iterated pullback used to construct the Chow chart product. -/
abbrev finiteProjectiveProduct {n : ℕ} (d : Fin n → ℕ) :=
  finProperProduct (Spec (.of k)) n (fun j ↦ space k (Fin (d j + 1)))
    (fun j ↦ baseProjection k (Fin (d j + 1))) (fun _ ↦ inferInstance)

/-- A constructed embedding of the actual product, retaining its base morphism. -/
structure FiniteSegreData {n : ℕ} (d : Fin n → ℕ) where
  /-- Dimension of the single target projective space. -/
  dimension : ℕ
  /-- The iterated Segre morphism. -/
  map : (finiteProjectiveProduct k d).obj ⟶ space k (Fin (dimension + 1))
  closed : IsClosedImmersion map
  over : map ≫ baseProjection k (Fin (dimension + 1)) =
    (finiteProjectiveProduct k d).base

/-- Construct the finite Segre embedding by adjoining one factor at a time. -/
def finiteSegreData : {n : ℕ} → (d : Fin n → ℕ) → FiniteSegreData k d
  | 0, _ =>
    { dimension := 0
      map := (zeroSpaceIso k).hom
      closed := inferInstance
      over := zeroSpaceIso_baseProjection k }
  | n + 1, d => by
    let E := finiteSegreData (fun j : Fin n ↦ d j.succ)
    let Q := finiteProjectiveProduct k (fun j : Fin n ↦ d j.succ)
    let p := baseProjection k (Fin (d 0 + 1))
    let q := baseProjection k (Fin (E.dimension + 1))
    let m : pullback p Q.base ⟶ pullback p q :=
      pullback.map p Q.base p q (𝟙 _) E.map (𝟙 _)
        (by simp) (by simpa using E.over.symm)
    have hm : IsClosedImmersion m :=
      MorphismProperty.pullbackMap (P := @IsClosedImmersion)
        (inferInstance : IsClosedImmersion (𝟙 _)) E.closed (by simp) E.over.symm
    refine
      { dimension := segreDimension (d 0) E.dimension
        map := m ≫ finiteSegreMorphism k (d 0) E.dimension
        closed := inferInstance
        over := ?_ }
    rw [Category.assoc, finiteSegreMorphism_baseProjection, ← Category.assoc]
    change m ≫ pullback.fst p q ≫ p = pullback.fst p Q.base ≫ p
    simp [m]

namespace ChartData

variable {k} {X : Scheme.{u}} {f : X ⟶ Spec (.of k)} (D : ChartData f)

/-- The constructed finite Segre data for the original enumerated chart family. -/
def projectiveSegreData :=
  finiteSegreData k (fun j ↦ D.dimension ((Fintype.equivFin D.Index).symm j))

/-- The dimension obtained by iterating binary Segre dimensions. -/
def projectiveSegreDimension : ℕ := D.projectiveSegreData.dimension

/-- Embed the original projective product, without replacing its underlying scheme. -/
def projectiveSegreEmbedding :
    D.projectiveProduct ⟶ space k (Fin (D.projectiveSegreDimension + 1)) :=
  D.projectiveSegreData.map

instance projectiveSegreEmbedding_isClosedImmersion :
    IsClosedImmersion D.projectiveSegreEmbedding := D.projectiveSegreData.closed

@[reassoc (attr := simp)]
lemma projectiveSegreEmbedding_baseProjection :
    D.projectiveSegreEmbedding ≫ baseProjection k (Fin (D.projectiveSegreDimension + 1)) =
      D.projectiveProductProjection := D.projectiveSegreData.over

end ChartData

section Immersion

variable {k} {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]

/-- The dimension of the projective target of the Chow modification. -/
def graphProjectiveDimension : ℕ := (chartData f).projectiveSegreDimension

/-- The Chow modification maps to one projective space by the finite Segre embedding. -/
def graphProjectiveImmersion :
    graphClosure f ⟶ space k (Fin (graphProjectiveDimension f + 1)) :=
  graphClosureToProduct f ≫ (chartData f).projectiveSegreEmbedding

instance graphProjectiveImmersion_isImmersion : IsImmersion (graphProjectiveImmersion f) := by
  dsimp [graphProjectiveImmersion]
  infer_instance

/-- The projective immersion retains the original structure map of the modification. -/
@[reassoc (attr := simp)]
lemma graphProjectiveImmersion_baseProjection :
    graphProjectiveImmersion f ≫ baseProjection k (Fin (graphProjectiveDimension f + 1)) =
      graphClosureπ f ≫ f := by
  dsimp only [graphProjectiveImmersion, graphProjectiveDimension]
  rw [Category.assoc,
    ChartData.projectiveSegreEmbedding_baseProjection, graphClosureToProduct_projection]

/-- On the dense common open the map is the Segre image of the original chart tuple. -/
@[reassoc]
lemma commonToGraphClosure_projectiveImmersion :
    commonToGraphClosure f ≫ graphProjectiveImmersion f =
      (chartData f).commonToProduct ≫ (chartData f).projectiveSegreEmbedding := by
  rw [graphProjectiveImmersion, ← Category.assoc, commonToGraphClosure_toProduct]

end Immersion

variable {k} {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]

/-- Properness of the original source makes the projective immersion proper. -/
instance graphProjectiveImmersion_isProper :
    IsProper (graphProjectiveImmersion f) := by
  have : IsProper (graphProjectiveImmersion f ≫
      baseProjection k (Fin (graphProjectiveDimension f + 1))) := by
    rw [graphProjectiveImmersion_baseProjection]
    infer_instance
  exact IsProper.of_comp _ (baseProjection k (Fin (graphProjectiveDimension f + 1)))

/-- A proper source gives the constructed closed projective embedding of its modification. -/
instance graphProjectiveImmersion_isClosedImmersion :
    IsClosedImmersion (graphProjectiveImmersion f) :=
  IsClosedImmersion.of_isPreimmersion _
    (graphProjectiveImmersion f).isClosedMap.isClosed_range

end FLT.Mazur.Chow
