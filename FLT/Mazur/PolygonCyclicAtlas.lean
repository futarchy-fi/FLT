/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonNodeBranches
public import FLT.Mazur.ProjectiveLineCharts
public import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# The cyclic open atlas with at least two nodes

Each Laurent edge joins the left branch of its node to the right branch of
its predecessor, with inverse coordinate. Branch disjointness makes this
multispan locally directed. Mathlib supplies the glue data and its cocycle.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace FLT.Mazur.PolygonCyclicAtlas

/-- Edges run from a node to its cyclic predecessor. -/
def shape (n : ℕ) : MultispanShape where
  L := Fin n
  R := Fin n
  fst := id
  snd := (finRotate n).symm

/-- A cyclic predecessor differs from its node when there are at least two nodes. -/
theorem prev_ne {n : ℕ} (h : 2 ≤ n) (i : Fin n) : (finRotate n).symm i ≠ i := by
  let : NeZero n := ⟨by omega⟩
  intro e
  have he := congrArg (finRotate n) e
  simp only [Equiv.apply_symm_apply, finRotate_apply] at he
  have hv := congrArg Fin.val he
  change i.val = (i.val + 1 % n) % n at hv
  rw [Nat.mod_eq_of_lt (by omega : 1 < n)] at hv
  have hi := i.isLt
  by_cases hl : i.val + 1 < n
  · rw [Nat.mod_eq_of_lt hl] at hv
    omega
  · have hl' : i.val + 1 = n := by omega
    rw [hl', Nat.mod_self] at hv
    omega

instance shape_thin (n : ℕ) [Fact (2 ≤ n)] : Quiver.IsThin (WalkingMultispan (shape n)) := by
  have aux : ∀ {a b c d : WalkingMultispan (shape n)} (f : a ⟶ b) (g : c ⟶ d),
      a = c → b = d → HEq f g := by
    intro a b c d f g
    cases f <;> cases g <;> intro h₁ h₂ <;>
      (try simp only [WalkingMultispan.left.injEq] at h₁) <;> subst_vars <;>
      simp_all only [shape, reduceCtorEq] <;> try exact HEq.rfl
    · exact False.elim (prev_ne (Fact.out : 2 ≤ n) _ (WalkingMultispan.right.inj h₂.symm))
    · exact False.elim (prev_ne (Fact.out : 2 ≤ n) _ (WalkingMultispan.right.inj h₂))
  exact fun _ _ ↦ ⟨fun f g ↦ eq_of_heq (aux f g rfl rfl)⟩

variable (K : Type u) [Field K] (n : ℕ)

/-- The actual punctured branches used in the cyclic gluing. -/
def index : MultispanIndex (shape n) Scheme where
  left _ := ProjectiveLine.overlap K
  right _ := PolygonNodeBranches.node K
  fst _ := PolygonNodeBranches.left K
  snd _ := (ProjectiveLine.inversion K).hom ≫ PolygonNodeBranches.right K

/-- The cyclic diagram of node charts and Laurent edges. -/
def diagram : WalkingMultispan (shape n) ⥤ Scheme := (index K n).multispan

instance map_isOpenImmersion {i j : WalkingMultispan (shape n)} (f : i ⟶ j) :
    IsOpenImmersion ((diagram K n).map f) := by
  cases f with
  | id i => change IsOpenImmersion (𝟙 _); infer_instance
  | fst i => exact PolygonNodeBranches.left_isOpenImmersion K
  | snd i =>
    change IsOpenImmersion ((ProjectiveLine.inversion K).hom ≫ PolygonNodeBranches.right K)
    infer_instance

instance diagram_locallyDirected : ((diagram K n) ⋙ Scheme.forget).IsLocallyDirected := by
  have aux : ∀ {i j k k' : WalkingMultispan (shape n)} (fi : i ⟶ k) (fj : j ⟶ k')
      (xi : (diagram K n ⋙ Scheme.forget).obj i)
      (xj : (diagram K n ⋙ Scheme.forget).obj j), k = k' →
      HEq ((diagram K n ⋙ Scheme.forget).map fi xi)
        ((diagram K n ⋙ Scheme.forget).map fj xj) →
      ∃ (l : WalkingMultispan (shape n)) (fli : l ⟶ i) (flj : l ⟶ j)
        (x : (diagram K n ⋙ Scheme.forget).obj l),
        (diagram K n ⋙ Scheme.forget).map fli x = xi ∧
        (diagram K n ⋙ Scheme.forget).map flj x = xj := by
    intro i j k k' fi fj
    cases fi with
    | id i =>
      intro xi xj hk he
      subst k'
      exact ⟨j, fj, 𝟙 _, xj, (eq_of_heq he).symm, rfl⟩
    | fst a =>
      cases fj with
      | id j =>
        intro xi xj hk he
        subst j
        exact ⟨_, 𝟙 _, .fst a, xi, rfl, eq_of_heq he⟩
      | fst b =>
        intro xi xj hk he
        have hab : a = b := WalkingMultispan.right.inj hk
        subst b
        have hx := (PolygonNodeBranches.left K).isOpenEmbedding.injective (eq_of_heq he)
        exact ⟨_, 𝟙 _, 𝟙 _, xi, rfl, hx⟩
      | snd b =>
        intro xi xj hk he
        exact False.elim ((Set.disjoint_left.mp (PolygonNodeBranches.disjoint_ranges K))
          ⟨xi, rfl⟩ ⟨(ProjectiveLine.inversion K).hom xj, (eq_of_heq he).symm⟩)
    | snd a =>
      cases fj with
      | id j =>
        intro xi xj hk he
        subst j
        exact ⟨_, 𝟙 _, .snd a, xi, rfl, eq_of_heq he⟩
      | fst b =>
        intro xi xj hk he
        exact False.elim ((Set.disjoint_left.mp (PolygonNodeBranches.disjoint_ranges K))
          ⟨xj, eq_of_heq he |>.symm⟩ ⟨(ProjectiveLine.inversion K).hom xi, rfl⟩)
      | snd b =>
        intro xi xj hk he
        have hab : a = b := (finRotate n).symm.injective (WalkingMultispan.right.inj hk)
        subst b
        have hx := ((ProjectiveLine.inversion K).hom ≫
          PolygonNodeBranches.right K).isOpenEmbedding.injective (eq_of_heq he)
        exact ⟨_, 𝟙 _, 𝟙 _, xi, rfl, hx⟩
  exact ⟨fun fi fj xi xj he ↦ aux fi fj xi xj rfl (heq_of_eq he)⟩

variable (h : 2 ≤ n)

/-- The scheme obtained by gluing the cyclic node charts. -/
def scheme : Scheme.{u} :=
  letI : Fact (2 ≤ n) := ⟨h⟩
  colimit (diagram K n)

/-- The inclusion of a node chart. -/
def chart (i : Fin n) : PolygonNodeBranches.node K ⟶ scheme K n h :=
  letI : Fact (2 ≤ n) := ⟨h⟩
  colimit.ι (diagram K n) (.right i)

instance chart_isOpenImmersion (i : Fin n) : IsOpenImmersion (chart K n h i) := by
  let : Fact (2 ≤ n) := ⟨h⟩
  exact inferInstanceAs (IsOpenImmersion (colimit.ι (diagram K n) (.right i)))

/-- The two coordinate inclusions of an edge agree in the glued scheme. -/
@[reassoc]
theorem overlap (i : Fin n) :
    PolygonNodeBranches.left K ≫ chart K n h i =
      (ProjectiveLine.inversion K).hom ≫ PolygonNodeBranches.right K ≫
        chart K n h ((finRotate n).symm i) := by
  let : Fact (2 ≤ n) := ⟨h⟩
  exact (colimit.w (diagram K n) (WalkingMultispan.Hom.fst i)).trans
    (colimit.w (diagram K n) (WalkingMultispan.Hom.snd i)).symm

/-- The node charts cover the scheme; the edges add no extra points. -/
theorem charts_cover (x : scheme K n h) : ∃ i y, chart K n h i y = x := by
  let : Fact (2 ≤ n) := ⟨h⟩
  obtain ⟨j, y, hy⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective (diagram K n) x
  cases j with
  | right i => exact ⟨i, y, hy⟩
  | left i =>
    refine ⟨i, PolygonNodeBranches.left K y, ?_⟩
    change ((diagram K n).map (WalkingMultispan.Hom.fst i) ≫
      colimit.ι (diagram K n) (.right i)) y = x
    exact (congrArg (fun f ↦ f y)
      (colimit.w (diagram K n) (WalkingMultispan.Hom.fst i))).trans hy

/-- Distinct node charts intersect precisely along their two possible cyclic edges. -/
theorem charts_eq_iff {i j : Fin n} (hne : i ≠ j)
    (x y : PolygonNodeBranches.node K) :
    chart K n h i x = chart K n h j y ↔
      (∃ z : ProjectiveLine.overlap K, (finRotate n).symm i = j ∧
        PolygonNodeBranches.left K z = x ∧
        ((ProjectiveLine.inversion K).hom ≫ PolygonNodeBranches.right K) z = y) ∨
      (∃ z : ProjectiveLine.overlap K, (finRotate n).symm j = i ∧
        ((ProjectiveLine.inversion K).hom ≫ PolygonNodeBranches.right K) z = x ∧
        PolygonNodeBranches.left K z = y) := by
  let : Fact (2 ≤ n) := ⟨h⟩
  constructor
  · intro he
    obtain ⟨k, fi, fj, z, hx, hy⟩ :=
      (Scheme.IsLocallyDirected.ι_eq_ι_iff (diagram K n)).mp he
    cases fi with
    | id _ =>
      cases fj
      exact (hne rfl).elim
    | fst a =>
      cases fj with
      | fst _ => exact (hne rfl).elim
      | snd _ => exact Or.inl ⟨z, rfl, hx, hy⟩
    | snd a =>
      cases fj with
      | fst _ => exact Or.inr ⟨z, rfl, hx, hy⟩
      | snd _ => exact (hne rfl).elim
  · rintro (⟨z, rfl, rfl, rfl⟩ | ⟨z, rfl, rfl, rfl⟩)
    · exact congrArg (fun f ↦ f z) (overlap K n h i)
    · exact (congrArg (fun f ↦ f z) (overlap K n h j)).symm

/-- Both cyclic edges occur in the intersection of the two charts of the two-gon. -/
theorem two_charts_eq_iff (x y : PolygonNodeBranches.node K) :
    chart K 2 (by decide) 0 x = chart K 2 (by decide) 1 y ↔
      (∃ z : ProjectiveLine.overlap K, PolygonNodeBranches.left K z = x ∧
        ((ProjectiveLine.inversion K).hom ≫ PolygonNodeBranches.right K) z = y) ∨
      (∃ z : ProjectiveLine.overlap K,
        ((ProjectiveLine.inversion K).hom ≫ PolygonNodeBranches.right K) z = x ∧
        PolygonNodeBranches.left K z = y) := by
  simpa only [show (finRotate 2).symm 0 = 1 from by decide,
    show (finRotate 2).symm 1 = 0 from by decide, true_and] using
      charts_eq_iff K 2 (by decide) (i := 0) (j := 1) (by decide) x y

/-- Inversion preserves the Laurent structure morphism. -/
@[reassoc]
theorem inversion_toBase :
    (ProjectiveLine.inversion K).hom ≫ (MultiplicativeGroupScheme.gm K).hom =
      (MultiplicativeGroupScheme.gm K).hom := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  ext r
  simp

/-- The compatible structure morphisms on all node charts and edges. -/
def baseCocone : Cocone (diagram K n) where
  pt := Spec (.of K)
  ι.app j := match j with
    | .left _ => (MultiplicativeGroupScheme.gm K).hom
    | .right _ => PolygonNodeBranches.toBase K
  ι.naturality := by
    intro i j f
    cases f with
    | id i => simp
    | fst i => exact (PolygonNodeBranches.left_toBase K).trans (Category.comp_id _).symm
    | snd i =>
      change ((ProjectiveLine.inversion K).hom ≫ PolygonNodeBranches.right K) ≫
        PolygonNodeBranches.toBase K = _ ≫ 𝟙 _
      exact (Category.assoc _ _ _).trans
        ((congrArg (fun f ↦ (ProjectiveLine.inversion K).hom ≫ f)
          (PolygonNodeBranches.right_toBase K)).trans
          ((inversion_toBase K).trans (Category.comp_id _).symm))

/-- The structure morphism on the glued scheme. -/
def toBase : scheme K n h ⟶ Spec (.of K) :=
  letI : Fact (2 ≤ n) := ⟨h⟩
  colimit.desc (diagram K n) (baseCocone K n)

@[reassoc (attr := simp)]
theorem chart_toBase (i : Fin n) :
    chart K n h i ≫ toBase K n h = PolygonNodeBranches.toBase K := by
  let : Fact (2 ≤ n) := ⟨h⟩
  exact colimit.ι_desc (baseCocone K n) (.right i)

end FLT.Mazur.PolygonCyclicAtlas
