/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ChowFiniteSegreEmbedding
public import FLT.Mazur.ChowAffineBaseGraphProductComparison

/-!
# A projective embedding of the affine-base Chow modification

Iterated Segre embeddings work over any commutative ring. Applying them
to the actual affine-base chart product gives an immersion; properness
of the original family makes this immersion closed.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

set_option backward.isDefEq.respectTransparency false

namespace FLT.Mazur.Chow.AffineBase

open ProjectiveSpace

variable (k : Type u) [CommRing k]

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

variable {R : CommRingCat.{u}} {X : Scheme.{u}} {f : X ⟶ Spec R} (D : ChartData f)

/-- The constructed finite Segre data for the original enumerated chart family. -/
def projectiveSegreData :=
  finiteSegreData R (fun j ↦ D.dimension ((Fintype.equivFin D.Index).symm j))

/-- The dimension obtained by iterating binary Segre dimensions. -/
def projectiveSegreDimension : ℕ := D.projectiveSegreData.dimension

/-- Embed the original projective product, without replacing its underlying scheme. -/
def projectiveSegreEmbedding :
    D.projectiveProduct ⟶ space R (Fin (D.projectiveSegreDimension + 1)) :=
  D.projectiveSegreData.map

instance projectiveSegreEmbedding_isClosedImmersion :
    IsClosedImmersion D.projectiveSegreEmbedding := D.projectiveSegreData.closed

@[reassoc (attr := simp)]
lemma projectiveSegreEmbedding_baseProjection :
    D.projectiveSegreEmbedding ≫ baseProjection R (Fin (D.projectiveSegreDimension + 1)) =
      D.projectiveProductProjection := D.projectiveSegreData.over

end ChartData

section Immersion

variable {R : CommRingCat.{u}} [IsNoetherianRing R] {X : Scheme.{u}} (f : X ⟶ Spec R)
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]

/-- The dimension of the projective target of the Chow modification. -/
def graphProjectiveDimension : ℕ := (chartData f).projectiveSegreDimension

/-- The Chow modification maps to one projective space by the finite Segre embedding. -/
def graphProjectiveImmersion :
    graphClosure f ⟶ space R (Fin (graphProjectiveDimension f + 1)) :=
  graphClosureToProduct f ≫ (chartData f).projectiveSegreEmbedding

instance graphProjectiveImmersion_isImmersion : IsImmersion (graphProjectiveImmersion f) := by
  dsimp [graphProjectiveImmersion]
  infer_instance

/-- The projective immersion retains the original structure map of the modification. -/
@[reassoc (attr := simp)]
lemma graphProjectiveImmersion_baseProjection :
    graphProjectiveImmersion f ≫ baseProjection R (Fin (graphProjectiveDimension f + 1)) =
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

variable {R : CommRingCat.{u}} [IsNoetherianRing R] {X : Scheme.{u}} (f : X ⟶ Spec R) [IsProper f]

/-- Properness of the original source makes the projective immersion proper. -/
instance graphProjectiveImmersion_isProper :
    IsProper (graphProjectiveImmersion f) := by
  have : IsProper (graphProjectiveImmersion f ≫
      baseProjection R (Fin (graphProjectiveDimension f + 1))) := by
    rw [graphProjectiveImmersion_baseProjection]
    infer_instance
  exact IsProper.of_comp _ (baseProjection R (Fin (graphProjectiveDimension f + 1)))

/-- A proper source gives the constructed closed projective embedding of its modification. -/
instance graphProjectiveImmersion_isClosedImmersion :
    IsClosedImmersion (graphProjectiveImmersion f) :=
  IsClosedImmersion.of_isPreimmersion _
    (graphProjectiveImmersion f).isClosedMap.isClosed_range

end FLT.Mazur.Chow.AffineBase
