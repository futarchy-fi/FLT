/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CoherentGenericComparison
public import FLT.Mazur.CoherentSubmoduleExtension
public import Mathlib.Algebra.Category.ModuleCat.Biproducts

/-!
# Extending a local coherent comparison by its graph

The graph of a local comparison extends to a coherent submodule of the global
direct sum. Its projections recover the prescribed comparison on stalks.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open Scheme.Modules FLT.Mazur.FCurve FLT.Mazur.FCurve.CoherentDevissage
open FLT.Mazur.CoherentSubmoduleEnlargement
universe u
namespace FLT.Mazur.CoherentGenericExtension

attribute [local instance] preservesBinaryBiproducts_of_preservesBinaryProducts
  preservesBinaryBiproducts_of_preservesBinaryCoproducts

/-- Finite direct sums of coherent sheaves on a Noetherian spectrum are coherent. -/
lemma affine_biprod_coherent {R : CommRingCat.{u}} [IsNoetherianRing R]
    (M N : (Spec R).Modules) [M.IsFinitePresentation] [N.IsFinitePresentation] :
    (M ⊞ N).IsFinitePresentation := by
  let A := moduleSpecΓFunctor.obj M
  let B := moduleSpecΓFunctor.obj N
  have : Module.Finite R A := affineCoherent_finite_sections M
  have : Module.Finite R B := affineCoherent_finite_sections N
  have : Module.Finite R (A ⊞ B : ModuleCat R) :=
    Module.Finite.equiv (ModuleCat.biprodIsoProd A B).symm.toLinearEquiv
  let e := (tilde.functor R).mapBiprod A B ≪≫
    biprod.mapIso (affineCoherentIso M).symm (affineCoherentIso N).symm
  exact (SheafOfModules.isFinitePresentation (Spec R).ringCatSheaf).prop_of_iso e
    (affineTilde_isFinitePresentation_of_finite (A ⊞ B))

/-- The ambient direct sum for the graph is coherent. -/
lemma biprod_coherent {X : Scheme.{u}} [IsLocallyNoetherian X]
    (M N : X.Modules) [M.IsFinitePresentation] [N.IsFinitePresentation] :
    (M ⊞ N).IsFinitePresentation := by
  apply coherentPresentation_of_affine_restrict
  intro U
  have : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  have := coherentPresentation_restrict U.2.fromSpec M
  have := coherentPresentation_restrict U.2.fromSpec N
  exact (SheafOfModules.isFinitePresentation (Spec Γ(X, U.1)).ringCatSheaf).prop_of_iso
    ((restrictFunctor U.2.fromSpec).mapBiprod M N).symm
    (affine_biprod_coherent _ _)

/-- The global extension theorem also applies to a neighborhood given by an open immersion. -/
theorem exists_extension_along {X Y : Scheme.{u}} [IsNoetherian X]
    (j : Y ⟶ X) [IsOpenImmersion j] (M : X.Modules) [M.IsFinitePresentation]
    (L : Y.Modules) [L.IsFinitePresentation] (a : L ⟶ M.restrict j) [Mono a] :
    ∃ (P : X.Modules) (_ : P.IsFinitePresentation) (b : P ⟶ M) (_ : Mono b)
      (e : P.restrict j ≅ L), e.hom ≫ a = (restrictFunctor j).map b := by
  let U := j.opensRange
  let k := j.isoOpensRange.inv
  let F := restrictFunctor k
  let q := (restrictFunctorComp k j).symm ≪≫
    restrictFunctorCongr j.isoOpensRange_inv_comp
  let a' := F.map a ≫ q.hom.app M
  have := coherentPresentation_restrict k L
  have := restrictMap_mono k a
  have : Mono a' := by dsimp [a']; infer_instance
  obtain ⟨E⟩ := CoherentSubmoduleExtension.exists_extension M U (L.restrict k) a'
  have (T : Y.Modules) : IsIso ((restrictAdjunction k).unit.app T) := iso_unit_isIso k T
  have : IsIso (restrictAdjunction k).unit := NatIso.isIso_of_isIso_app _
  let FF := (restrictAdjunction k).fullyFaithfulLOfIsIsoUnit
  let e := FF.preimageIso (q.app E.obj ≪≫ E.comparison)
  refine ⟨E.obj, E.coherent, E.inclusion, E.inclusion_mono, e, ?_⟩
  apply FF.map_injective
  apply (cancel_mono (q.hom.app M)).mp
  simp only [Functor.map_comp, Category.assoc]
  have he : F.map e.hom = q.hom.app E.obj ≫ E.comparison.hom := FF.map_preimage _
  rw [he, Category.assoc]
  change q.hom.app E.obj ≫ E.comparison.hom ≫ a' = _
  rw [E.commutes]
  exact (q.hom.naturality E.inclusion).symm

variable {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j] (M N : X.Modules)

/-- The actual graph inclusion in the restriction of the ambient direct sum. -/
def graph (g : M.restrict j ⟶ N.restrict j) :
    M.restrict j ⟶ (M ⊞ N).restrict j :=
  biprod.lift (𝟙 _) g ≫ ((restrictFunctor j).mapBiprod M N).inv

instance graph_mono (g : M.restrict j ⟶ N.restrict j) : Mono (graph j M N g) := by
  dsimp only [graph]
  infer_instance

/-- The first graph projection is the identity. -/
lemma graph_fst (g : M.restrict j ⟶ N.restrict j) :
    graph j M N g ≫ (restrictFunctor j).map biprod.fst = 𝟙 _ := by
  have h : ((restrictFunctor j).mapBiprod M N).hom ≫ biprod.fst =
      (restrictFunctor j).map biprod.fst := by simp
  rw [graph, Category.assoc, ← h, Iso.inv_hom_id_assoc, biprod.lift_fst]

/-- The second graph projection is the given local comparison. -/
lemma graph_snd (g : M.restrict j ⟶ N.restrict j) :
    graph j M N g ≫ (restrictFunctor j).map biprod.snd = g := by
  have h : ((restrictFunctor j).mapBiprod M N).hom ≫ biprod.snd =
      (restrictFunctor j).map biprod.snd := by simp
  rw [graph, Category.assoc, ← h, Iso.inv_hom_id_assoc, biprod.lift_snd]

/-- Extend the graph, preserving its inclusion and both projection squares. -/
theorem exists_graph_extension [IsNoetherian X]
    [M.IsFinitePresentation] [N.IsFinitePresentation]
    (g : M.restrict j ⟶ N.restrict j) :
    ∃ (P : X.Modules) (_ : P.IsFinitePresentation) (b : P ⟶ M ⊞ N) (_ : Mono b)
      (e : P.restrict j ≅ M.restrict j),
      e.hom ≫ graph j M N g = (restrictFunctor j).map b ∧
      (restrictFunctor j).map (b ≫ biprod.fst) = e.hom ∧
      (restrictFunctor j).map (b ≫ biprod.snd) = e.hom ≫ g := by
  have := biprod_coherent M N
  have := coherentPresentation_restrict j M
  obtain ⟨P, hP, b, hb, e, he⟩ := exists_extension_along j (M ⊞ N)
    (M.restrict j) (graph j M N g)
  refine ⟨P, hP, b, hb, e, he, ?_, ?_⟩
  · rw [Functor.map_comp, ← he, Category.assoc, graph_fst, Category.comp_id]
  · rw [Functor.map_comp, ← he, Category.assoc, graph_snd]

/-- Restriction coordinates at an identified point are natural in global morphisms. -/
lemma stalkAt_naturality (y : Y) (x : X) (hx : j y = x) {P Q : X.Modules}
    (a : P ⟶ Q) (m : (P.restrict j).presheaf.stalk y) :
    comparisonStalkAt j y x hx Q ((stalk y).map ((restrictFunctor j).map a) m) =
      (stalk x).map a (comparisonStalkAt j y x hx P m) := by
  subst x
  simpa [comparisonStalkAt] using comparisonRestrictStalk_naturality j y a m

variable (x : X)

/-- A global coherent graph whose projections realize the prescribed stalk map. -/
structure ComparisonExtension
    (f : M.presheaf.stalk x →ₗ[X.presheaf.stalk x] N.presheaf.stalk x) where
  /-- The coherent module extending the local graph. -/
  obj : X.Modules
  /-- The graph extension has finite local presentations. -/
  coherent : obj.IsFinitePresentation
  /-- The graph remains a subobject of the global direct sum. -/
  inclusion : obj ⟶ M ⊞ N
  /-- Its inclusion is monic. -/
  inclusion_mono : Mono inclusion
  /-- The first projection identifies the common stalk with the source stalk. -/
  first_isIso : IsIso ((stalk x).map (inclusion ≫ biprod.fst))
  /-- The second projection agrees exactly with the prescribed map through the first. -/
  germ : ∀ m, (stalk x).map (inclusion ≫ biprod.snd) m =
    f ((stalk x).map (inclusion ≫ biprod.fst) m)

attribute [instance] ComparisonExtension.coherent ComparisonExtension.inclusion_mono
  ComparisonExtension.first_isIso

/-- Construct a global comparison through a coherent graph from any prescribed stalk map. -/
theorem exists_comparison_extension [IsNoetherian X]
    [M.IsFinitePresentation] [N.IsFinitePresentation]
    (f : M.presheaf.stalk x →ₗ[X.presheaf.stalk x] N.presheaf.stalk x) :
    Nonempty (ComparisonExtension M N x f) := by
  obtain ⟨C⟩ := exists_coherent_stalk_neighborhood M N x f
  obtain ⟨P, hP, b, hb, e, _, hfst, hsnd⟩ :=
    exists_graph_extension C.inclusion M N C.map
  let A := comparisonStalkAt C.inclusion C.point x C.point_eq P
  let B := comparisonStalkAt C.inclusion C.point x C.point_eq M
  let D := comparisonStalkAt C.inclusion C.point x C.point_eq N
  let t := ((stalk C.point).mapIso e).addCommGroupIsoToAddEquiv
  have hp (m) : (stalk x).map (b ≫ biprod.fst) (A m) = B (t m) := by
    rw [← stalkAt_naturality C.inclusion C.point x C.point_eq, hfst]
    rfl
  have hq (m) : (stalk x).map (b ≫ biprod.snd) (A m) =
      D ((stalk C.point).map C.map (t m)) := by
    rw [← stalkAt_naturality C.inclusion C.point x C.point_eq, hsnd, Functor.map_comp]
    rfl
  have hi : IsIso ((stalk x).map (b ≫ biprod.fst)) := by
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    constructor
    · intro m n h
      obtain ⟨v, rfl⟩ := A.surjective m
      obtain ⟨w, rfl⟩ := A.surjective n
      rw [hp, hp] at h
      exact congrArg A (t.injective (B.injective h))
    · intro m
      refine ⟨A (t.symm (B.symm m)), ?_⟩
      rw [hp]
      exact (congrArg B (t.apply_symm_apply _)).trans (B.apply_symm_apply m)
  refine ⟨⟨P, hP, b, hb, hi, ?_⟩⟩
  intro m
  obtain ⟨n, rfl⟩ := A.surjective m
  rw [hq, hp]
  exact C.germ (t n)

/-- When the prescribed map is an equivalence, both global projections are stalk isomorphisms. -/
instance ComparisonExtension.second_isIso
    {e : M.presheaf.stalk x ≃ₗ[X.presheaf.stalk x] N.presheaf.stalk x}
    (E : ComparisonExtension M N x e.toLinearMap) :
    IsIso ((stalk x).map (E.inclusion ≫ biprod.snd)) := by
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  have hp := ConcreteCategory.bijective_of_isIso ((stalk x).map (E.inclusion ≫ biprod.fst))
  constructor
  · intro m n h
    apply hp.injective
    apply e.injective
    exact (E.germ m).symm.trans (h.trans (E.germ n))
  · intro n
    obtain ⟨m, hm⟩ := hp.surjective (e.symm n)
    refine ⟨m, ?_⟩
    rw [E.germ, hm]
    exact e.apply_symm_apply n

/-- The construction applies to actual coherent closed pushforwards on the ambient scheme. -/
theorem exists_closed_comparison_extension {Z : Scheme.{u}} [IsNoetherian X]
    (i : Y ⟶ X) (k : Z ⟶ X) [IsClosedImmersion i] [IsClosedImmersion k]
    (P : Y.Modules) (Q : Z.Modules) [P.IsFinitePresentation] [Q.IsFinitePresentation]
    (f : ((pushforward i).obj P).presheaf.stalk x →ₗ[X.presheaf.stalk x]
      ((pushforward k).obj Q).presheaf.stalk x) :
    Nonempty (ComparisonExtension ((pushforward i).obj P) ((pushforward k).obj Q) x f) := by
  have := closedPushforward_isFinitePresentation i P
  have := closedPushforward_isFinitePresentation k Q
  exact exists_comparison_extension _ _ x f

end FLT.Mazur.CoherentGenericExtension
