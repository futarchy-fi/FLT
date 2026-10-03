/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PinchingChartBaseChange
public import FLT.Mazur.PolygonAtlasCocone
public import FLT.Mazur.OneGonGluing
/-!
# The polygon atlas after parameter base change

The cyclic charts become nodes over the parameter ring. The one-gon retains
its distinct equalizer chart and its torus chart. All are actual charts of the
specified pullback, and the covers include every positive polygon size.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped LaurentPolynomial TensorProduct
universe u
namespace FLT.Mazur.PolygonProductAtlas
open PinchingChartBaseChange
variable (K S : Type u) [Field K] [CommRing S] [Algebra K S]

/-- The original cyclic node atlas. -/
def cyclicCover (n : ℕ) (hn : 2 ≤ n) : (PolygonCyclicAtlas.scheme K n hn).OpenCover where
  I₀ := Fin n
  X _ := PolygonNodeBranches.node K
  f := PolygonCyclicAtlas.chart K n hn
  mem₀ := by
    rw [Scheme.ofArrows_mem_precoverage_iff]
    exact ⟨PolygonCyclicAtlas.charts_cover K n hn, fun _ ↦ inferInstance⟩

/-- The cyclic polygon after affine parameter base change. -/
abbrev cyclicProduct (n : ℕ) (hn : 2 ≤ n) :=
  pullback (parameter K S) (PolygonCyclicAtlas.toBase K n hn)
/-- Pull back the specified cyclic node atlas. -/
def cyclicPullbackCover (n : ℕ) (hn : 2 ≤ n) : (cyclicProduct K S n hn).OpenCover :=
  Scheme.Pullback.openCoverOfRight (cyclicCover K n hn) (parameter K S)
    (PolygonCyclicAtlas.toBase K n hn)
/-- Identify each pulled-back chart with the node over the parameter ring. -/
def cyclicChartIso (n : ℕ) (hn : 2 ≤ n) (i : Fin n) :
    (cyclicPullbackCover K S n hn).X i ≅ PolygonNodeBranches.node S :=
  pullback.congrHom rfl (PolygonCyclicAtlas.chart_toBase K n hn i) ≪≫ nodeProductIso K S

/-- The node chart in the actual pulled-back polygon. -/
def cyclicChartMap (n : ℕ) (hn : 2 ≤ n) (i : Fin n) :
    PolygonNodeBranches.node S ⟶ cyclicProduct K S n hn :=
  (cyclicChartIso K S n hn i).inv ≫ (cyclicPullbackCover K S n hn).f i
instance cyclicChartMap_open (n : ℕ) (hn : 2 ≤ n) (i : Fin n) :
    IsOpenImmersion (cyclicChartMap K S n hn i) := by
  unfold cyclicChartMap
  infer_instance
@[reassoc (attr := simp)] theorem cyclicChartMap_fst (n : ℕ) (hn : 2 ≤ n) (i : Fin n) :
    cyclicChartMap K S n hn i ≫ pullback.fst _ _ = nodeBase S := by
  simp only [cyclicChartMap, cyclicPullbackCover, cyclicCover, Scheme.Pullback.openCoverOfRight_X,
    cyclicChartIso, Iso.trans_inv, pullback.congrHom_inv,
    Scheme.Pullback.openCoverOfRight_f, Category.assoc, limit.lift_π, PullbackCone.mk_pt,
    PullbackCone.mk_π_app, Category.comp_id]
  exact nodeProductIso_inv_fst K S
@[reassoc (attr := simp)] theorem cyclicChartMap_snd (n : ℕ) (hn : 2 ≤ n) (i : Fin n) :
    cyclicChartMap K S n hn i ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom
        (PolygonNodeScalarExtension.coeffMap (R := K) (S := S)).toRingHom) ≫
          PolygonCyclicAtlas.chart K n hn i := by
  simp only [cyclicChartMap, cyclicPullbackCover, cyclicCover, Scheme.Pullback.openCoverOfRight_X,
    cyclicChartIso, Iso.trans_inv, pullback.congrHom_inv,
    Scheme.Pullback.openCoverOfRight_f, Category.assoc, limit.lift_π, PullbackCone.mk_pt,
    PullbackCone.mk_π_app, limit.lift_π_assoc, cospan_right, Category.comp_id,
    AlgHom.toRingHom_eq_coe]
  exact nodeProductIso_inv_snd_assoc K S _
/-- The covering family of node charts over the parameter ring. -/
def cyclicProductCover (n : ℕ) (hn : 2 ≤ n) : (cyclicProduct K S n hn).OpenCover :=
  (cyclicPullbackCover K S n hn).copy (Fin n) (fun _ ↦ PolygonNodeBranches.node S)
    (cyclicChartMap K S n hn) (Equiv.refl _) (fun i ↦ (cyclicChartIso K S n hn i).symm)
    (fun _ ↦ rfl)

/-- The equalizer and torus charts of the original one-gon. -/
def oneGonCover : (OneGonGluing.scheme K).OpenCover where
  I₀ := Bool
  X b := if b then OneGonGluing.torusChart K else OneGonGluing.nodeChart K
  f b := match b with
    | false => OneGonGluing.node K
    | true => OneGonGluing.torus K
  mem₀ := by
    rw [Scheme.ofArrows_mem_precoverage_iff]
    refine ⟨?_, ?_⟩
    · intro x
      rcases OneGonGluing.charts_cover K x with ⟨y, hy⟩ | ⟨y, hy⟩
      · exact ⟨false, y, hy⟩
      · exact ⟨true, y, hy⟩
    · intro b
      cases b <;> dsimp <;> infer_instance
/-- The one-gon after affine parameter base change. -/
abbrev oneGonProduct := pullback (parameter K S) (OneGonGluing.toBase K)
/-- Pull back the two original one-gon charts. -/
def oneGonPullbackCover : (oneGonProduct K S).OpenCover :=
  Scheme.Pullback.openCoverOfRight (oneGonCover K) (parameter K S) (OneGonGluing.toBase K)
/-- Coordinate spectra of the pulled-back one-gon charts. -/
def oneGonChart (b : Bool) : Scheme :=
  if b then Spec (.of (S ⊗[K] K[T;T⁻¹])) else Spec (.of (PolygonNodePresentation.B (R := S)))
/-- Identify the pulled-back charts with their coordinate spectra. -/
def oneGonChartIso (b : Bool) : (oneGonPullbackCover K S).X b ≅ oneGonChart K S b := by
  cases b
  · exact pullback.congrHom rfl (OneGonGluing.node_toBase K) ≪≫ oneGonProductIso K S
  · exact pullback.congrHom rfl (OneGonGluing.torus_toBase K) ≪≫ pullbackSpecIso K S K[T;T⁻¹]
/-- The coordinate chart map into the pulled-back one-gon. -/
def oneGonChartMap (b : Bool) : oneGonChart K S b ⟶ oneGonProduct K S :=
  (oneGonChartIso K S b).inv ≫ (oneGonPullbackCover K S).f b
instance oneGonChartMap_open (b : Bool) : IsOpenImmersion (oneGonChartMap K S b) := by
  unfold oneGonChartMap
  infer_instance
/-- The equalizer and tensor-torus charts cover the pulled-back one-gon. -/
def oneGonProductCover : (oneGonProduct K S).OpenCover :=
  (oneGonPullbackCover K S).copy Bool (oneGonChart K S) (oneGonChartMap K S)
    (Equiv.refl _) (fun b ↦ (oneGonChartIso K S b).symm) (fun _ ↦ rfl)
@[reassoc (attr := simp)] theorem oneGonNode_fst :
    oneGonChartMap K S false ≫ pullback.fst _ _ = oneGonBase S := by
  simp only [oneGonChartMap, oneGonPullbackCover, oneGonCover,
    Scheme.Pullback.openCoverOfRight_X, Bool.false_eq_true, ↓dreduceIte, oneGonChartIso,
    Iso.trans_inv, pullback.congrHom_inv,
    Scheme.Pullback.openCoverOfRight_f, Category.assoc, limit.lift_π, PullbackCone.mk_pt,
    PullbackCone.mk_π_app, Category.comp_id]
  exact oneGonProductIso_inv_fst K S
@[reassoc (attr := simp)] theorem oneGonNode_snd :
    oneGonChartMap K S false ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom
        (OneGonScalarExtension.coeffMap (R := K) (S := S)).toRingHom) ≫ OneGonGluing.node K := by
  simp only [oneGonChartMap, oneGonPullbackCover, oneGonCover,
    Scheme.Pullback.openCoverOfRight_X, Bool.false_eq_true, ↓dreduceIte, oneGonChartIso,
    Iso.trans_inv, pullback.congrHom_inv,
    Scheme.Pullback.openCoverOfRight_f, Category.assoc, limit.lift_π, PullbackCone.mk_pt,
    PullbackCone.mk_π_app, limit.lift_π_assoc, cospan_right, Category.comp_id,
    AlgHom.toRingHom_eq_coe]
  exact oneGonProductIso_inv_snd_assoc K S _
@[reassoc (attr := simp)] theorem oneGonTorus_fst :
    oneGonChartMap K S true ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (algebraMap S (S ⊗[K] K[T;T⁻¹]))) := by
  simp only [oneGonChartMap, oneGonPullbackCover, oneGonCover,
    Scheme.Pullback.openCoverOfRight_X, ↓dreduceIte, oneGonChartIso, Iso.trans_inv,
    pullback.congrHom_inv,
    Scheme.Pullback.openCoverOfRight_f, Category.assoc, limit.lift_π, PullbackCone.mk_pt,
    PullbackCone.mk_π_app, Category.comp_id]
  exact pullbackSpecIso_inv_fst' K S K[T;T⁻¹]
@[reassoc (attr := simp)] theorem oneGonTorus_snd :
    oneGonChartMap K S true ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : K[T;T⁻¹] →ₐ[K] S ⊗[K] K[T;T⁻¹]).toRingHom) ≫
          OneGonGluing.torus K := by
  simp only [oneGonChartMap, oneGonPullbackCover, oneGonCover,
    Scheme.Pullback.openCoverOfRight_X, ↓dreduceIte, oneGonChartIso, Iso.trans_inv,
    pullback.congrHom_inv,
    Scheme.Pullback.openCoverOfRight_f, Category.assoc, limit.lift_π, PullbackCone.mk_pt,
    PullbackCone.mk_π_app, limit.lift_π_assoc, cospan_right, Category.comp_id,
    AlgHom.toRingHom_eq_coe]
  exact pullbackSpecIso_inv_snd_assoc K S K[T;T⁻¹] _

/-- The actual product atlas for every positive polygon size. -/
def specifiedProductCover (n : ℕ) [NeZero n] :
    (pullback (parameter K S) (PolygonAtlas.polygon K n).hom).OpenCover := by
  rcases n with _ | (_ | n)
  · exact (NeZero.ne 0 rfl).elim
  · exact oneGonProductCover K S
  · exact cyclicProductCover K S (n + 2) (by omega)

/-- The original atlas for every positive polygon size. -/
def specifiedCover (n : ℕ) [NeZero n] : (PolygonAtlas.polygon K n).left.OpenCover := by
  rcases n with _ | (_ | n)
  · exact (NeZero.ne 0 rfl).elim
  · exact oneGonCover K
  · exact cyclicCover K (n + 2) (by omega)

/-- The original atlas pulled back along an arbitrary scheme morphism. -/
def pullbackCover (n : ℕ) [NeZero n] {T : Scheme.{u}} (g : T ⟶ Spec (.of K)) :
    (pullback g (PolygonAtlas.polygon K n).hom).OpenCover :=
  Scheme.Pullback.openCoverOfRight (specifiedCover K n) g (PolygonAtlas.polygon K n).hom
end FLT.Mazur.PolygonProductAtlas
