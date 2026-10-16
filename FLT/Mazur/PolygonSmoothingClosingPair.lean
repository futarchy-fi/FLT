/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonInfinitesimalAdjacentUnion
public import FLT.Mazur.WeierstrassDividedRetainedPolygonMaps

/-!
# Standard closing attachments inside the polygon

The reciprocal retained puncture and either terminal puncture form the
actual union of the last retained chart and chart zero. The opposite arm
uses the full branch swap and the same original retained index.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.PolygonSmoothing
open WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (R : Type) [CommRing R] (t : R) (j : ℕ)
local notation "l" => leftBranchOpen R t
local notation "r" => rightBranchOpen R t
local notation "e" => edgeInversion R
local notation "p" => precedingBranch R t
local notation "L" => Iso.hom (edgeInversion R) ≫ leftBranchOpen R t
local notation "c" => PolygonInfinitesimal.chart R t (2 * (j + 1) + 3) (by omega)
local notation "lastIdx" => fun b ↦
  retainedPolygonIndex (j + 1) (Fin.mk j (Nat.lt_succ_self j)) b
local notation "f" => retainedPolygonMap R t (j + 1) (Fin.mk j (Nat.lt_succ_self j))

/-- Reciprocal retained coordinates give the ordinary false-branch adjacent span. -/
def closingFalseSpanIso : pushout L r ≅ pushout l p :=
  asIso (pushout.map L r l p (𝟙 _) (𝟙 _) (e).hom (by simp) (by
    change r ≫ 𝟙 _ = (e).inv ≫ (e).hom ≫ r
    simp))

/-- The reciprocal retained edge becomes the preceding edge after the full swap. -/
@[reassoc] theorem closingTrueSpan_boundary : L ≫ (branchSwapIso R t).hom = p := by
  rw [Category.assoc, leftBranchOpen_branchSwapIso]
  rfl

/-- The full coordinate swap identifies the opposite ordered span. -/
def closingTrueOrientedSpanIso : pushout L l ≅ pushout p l :=
  asIso (pushout.map L l p l (branchSwapIso R t).hom (𝟙 _) (𝟙 _)
    (by rw [closingTrueSpan_boundary, Category.id_comp]) (by simp))

/-- The opposite retained branch becomes the preceding puncture. -/
def closingTrueSpanIso : pushout L l ≅ pushout l p :=
  closingTrueOrientedSpanIso R t ≪≫ pushoutSymmetry p l

@[reassoc (attr := simp)] theorem closingFalseSpanIso_retained :
    pushout.inl L r ≫ (closingFalseSpanIso R t).hom = pushout.inl l p := by
  simp [closingFalseSpanIso]

@[reassoc (attr := simp)] theorem closingFalseSpanIso_terminal :
    pushout.inr L r ≫ (closingFalseSpanIso R t).hom = pushout.inr l p := by
  simp [closingFalseSpanIso]

@[reassoc (attr := simp)] theorem closingTrueSpanIso_retained :
    pushout.inl L l ≫ (closingTrueSpanIso R t).hom =
      (branchSwapIso R t).hom ≫ pushout.inr l p := by
  simp [closingTrueSpanIso, closingTrueOrientedSpanIso]

@[reassoc (attr := simp)] theorem closingTrueSpanIso_terminal :
    pushout.inr L l ≫ (closingTrueSpanIso R t).hom = pushout.inl l p := by
  simp [closingTrueSpanIso, closingTrueOrientedSpanIso]

/-- The two possible terminal punctures. -/
def closingPairPuncture (b : Bool) : branchTorus R ⟶ chart R t :=
  if b then l else r

instance closingPairPuncture_isOpenImmersion (b : Bool) :
    IsOpenImmersion (closingPairPuncture R t b) := by
  cases b <;> dsimp [closingPairPuncture] <;> infer_instance

variable [Fact (IsNilpotent t)]

/-- Both standard closing pairs have explicit maps to the actual polygon. -/
def closingPairToPolygon (b : Bool) : pushout L (closingPairPuncture R t b) ⟶
    PolygonInfinitesimal.scheme R t (2 * (j + 1) + 3) (by omega) := by
  cases b
  · exact (closingFalseSpanIso R t).hom ≫
      PolygonInfinitesimal.adjacentToPolygon R t _ _ (lastIdx false) 0
        (retainedPolygonIndex_false_terminal j)
  · exact (closingTrueSpanIso R t).hom ≫
      PolygonInfinitesimal.adjacentToPolygon R t _ _ 0 (lastIdx true)
        (retainedPolygonIndex_true_terminal j)

/-- The retained restriction uses exactly its original branch and polygon label. -/
@[reassoc (attr := simp)] theorem closingPairToPolygon_retained (b : Bool) :
    pushout.inl L (closingPairPuncture R t b) ≫ closingPairToPolygon R t j b = f b := by
  cases b <;> simp [closingPairToPolygon, closingPairPuncture, retainedPolygonMap]

/-- Each pair contains the same full terminal polygon chart. -/
@[reassoc (attr := simp)] theorem closingPairToPolygon_terminal (b : Bool) :
    pushout.inr L (closingPairPuncture R t b) ≫ closingPairToPolygon R t j b = c 0 := by
  cases b <;> simp [closingPairToPolygon, closingPairPuncture]

/-- The closing pairs embed as open subschemes of the prescribed polygon. -/
instance closingPairToPolygon_isOpenImmersion (b : Bool) :
    IsOpenImmersion (closingPairToPolygon R t j b) := by
  have hf : lastIdx false = 1 := by ext; simp [retainedPolygonIndex]
  have ht : lastIdx true = ⟨2 * (j + 1) + 2, by omega⟩ := by
    ext
    simp only [retainedPolygonIndex, ↓reduceIte]
    omega
  have hfne : lastIdx false ≠ 0 := by
    rw [hf]; intro he; have hv := congrArg Fin.val he
    norm_num at hv
  have htne : (0 : Fin (2 * (j + 1) + 3)) ≠ lastIdx true := by
    rw [ht]
    intro he
    have hv := congrArg Fin.val he
    simp only [Fin.val_zero] at hv
    omega
  have hfr : (finRotate (2 * (j + 1) + 3)).symm 0 ≠ lastIdx false := by
    rw [retainedPolygonIndex_true_terminal, hf]
    intro he
    have hv := congrArg Fin.val he
    norm_num [retainedPolygonIndex] at hv
    omega
  have htr : (finRotate (2 * (j + 1) + 3)).symm (lastIdx true) ≠ 0 := by
    intro he
    have he' := (Equiv.symm_apply_eq _).mp he
    rw [ht] at he'
    have hv := congrArg Fin.val he'
    simp at hv
  cases b
  · let _ := PolygonInfinitesimal.adjacentToPolygon_isOpenImmersion R t
      (2 * (j + 1) + 3) (by omega)
      (lastIdx false) 0 (retainedPolygonIndex_false_terminal j) hfne hfr
    dsimp only [closingPairToPolygon, Bool.false_eq_true, ↓reduceIte]
    infer_instance
  · let _ := PolygonInfinitesimal.adjacentToPolygon_isOpenImmersion R t
      (2 * (j + 1) + 3) (by omega)
      0 (lastIdx true) (retainedPolygonIndex_true_terminal j) htne htr
    dsimp only [closingPairToPolygon, ↓reduceIte]
    infer_instance

/-- The full image consists of exactly the retained and terminal chart images. -/
theorem closingPairToPolygon_range (b : Bool) :
    Set.range (closingPairToPolygon R t j b) = Set.range (f b) ∪ Set.range (c 0) := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    rcases SchemeOpenPushout.charts_cover L (closingPairPuncture R t b) x with
      ⟨a, rfl⟩ | ⟨a, rfl⟩
    · exact Or.inl ⟨a, (congrArg (fun g ↦ g a)
        (closingPairToPolygon_retained R t j b)).symm⟩
    · exact Or.inr ⟨a, (congrArg (fun g ↦ g a)
        (closingPairToPolygon_terminal R t j b)).symm⟩
  · rintro (⟨a, rfl⟩ | ⟨a, rfl⟩)
    · exact ⟨pushout.inl L (closingPairPuncture R t b) a, congrArg (fun g ↦ g a)
        (closingPairToPolygon_retained R t j b)⟩
    · exact ⟨pushout.inr L (closingPairPuncture R t b) a, congrArg (fun g ↦ g a)
        (closingPairToPolygon_terminal R t j b)⟩

/-- Each complete closing attachment is its actual two-chart polygon union. -/
def closingPairUnionIso (b : Bool) : pushout L (closingPairPuncture R t b) ≅
    ((f b).opensRange ⊔ (c 0).opensRange).toScheme :=
  IsOpenImmersion.isoOfRangeEq (closingPairToPolygon R t j b)
    ((f b).opensRange ⊔ (c 0).opensRange).ι (by
      rw [Scheme.Opens.range_ι, closingPairToPolygon_range]
      rfl)

@[reassoc] theorem closingPairUnionIso_polygon (b : Bool) :
    (closingPairUnionIso R t j b).hom ≫ ((f b).opensRange ⊔ (c 0).opensRange).ι =
      closingPairToPolygon R t j b :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

end FLT.Mazur.PolygonSmoothing
