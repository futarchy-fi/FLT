/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertBoundaryThickeningTests

/-!
# Full original Picard kernel pairs on infinitesimal neighborhoods

The closed boundary relation represents equality of the original Picard
sections on every test. Reflexivity, symmetry and composition are scheme
morphisms, with no quotient effectivity assumed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve SchemeOpenEnvelope
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
local notation "π" => Over.Hom.left (prod.fst : prod A V ⟶ A)
local notation "O" => Scheme.Hom.opensRange (Over.Hom.left (toEnvelope f hL d V c k))
variable (n : ℕ)
local notation "B" => originalThickenedSource f hL d V c k n
local notation "i" => originalThickenedSourceMap f hL d V c k n
local notation "D" => relation f hL d V c k
local notation "p" => fst f hL d V c k
local notation "q" => snd f hL d V c k

local notation "C" => originalThickenedRelation f hL d V c k n
local notation "r" => originalThickenedFst f hL d V c k n
local notation "s" => originalThickenedSnd f hL d V c k n
local notation "z" => originalThickenedArrow f hL d V c k n

attribute [local irreducible] originalThickenedRelation originalThickenedFst originalThickenedSnd
  originalThickenedArrow originalThickenedSource originalThickenedSourceMap
local notation "σ" => originalThickenedSection f hL d V c k n

/-- Equal original classes along the closed relation remain equal after any test map. -/
theorem originalThickened_class_natural {T : Over (Spec (.of R))} (a : T ⟶ C) :
    (relativeFppfSheaf f).obj.map (a ≫ r).op σ =
      (relativeFppfSheaf f).obj.map (a ≫ s).op σ := by
  simpa only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply] using
    congrArg ((relativeFppfSheaf f).obj.map a.op) (originalThickened_equal_class f hL d V c k n)

/-- The full presheaf kernel pair of the original section on the closed boundary. -/
theorem originalThickened_isPullback : IsPullback (uliftYoneda.{1}.map r) (uliftYoneda.{1}.map s)
    ((uliftYonedaEquiv (F := (relativeFppfSheaf f).obj ⋙ forget CommGrpCat)).symm σ)
    ((uliftYonedaEquiv (F := (relativeFppfSheaf f).obj ⋙ forget CommGrpCat)).symm σ) := by
  apply IsPullback.of_forall_isPullback_app
  intro T
  rw [Types.isPullback_iff]
  refine ⟨?_, ?_, ?_⟩
  · apply ConcreteCategory.hom_ext
    intro a
    exact originalThickened_class_natural f hL d V c k n a.down
  · intro a b h
    exact ULift.ext (originalThickened_hom_ext f hL d V c k n
      (congrArg ULift.down h.1) (congrArg ULift.down h.2))
  · intro a b h
    obtain ⟨w, hw, _⟩ := originalThickened_lift f hL d V c k n a.down b.down h
    exact ⟨ULift.up w, ULift.ext hw.1, ULift.ext hw.2⟩

/-- The unique closed arrow with the prescribed equal-class endpoints. -/
def originalThickenedTestArrow {T : Over (Spec (.of R))} (a b : T ⟶ B)
    (h : (relativeFppfSheaf f).obj.map a.op σ = (relativeFppfSheaf f).obj.map b.op σ) :
    T ⟶ C := (originalThickened_lift f hL d V c k n a b h).choose

/-- The first whole closed endpoint is retained. -/
@[reassoc]
theorem originalThickenedTestArrow_fst {T : Over (Spec (.of R))} (a b : T ⟶ B) (h) :
    originalThickenedTestArrow f hL d V c k n a b h ≫ r = a :=
  (originalThickened_lift f hL d V c k n a b h).choose_spec.1.1

/-- The independent second whole closed endpoint is retained. -/
@[reassoc]
theorem originalThickenedTestArrow_snd {T : Over (Spec (.of R))} (a b : T ⟶ B) (h) :
    originalThickenedTestArrow f hL d V c k n a b h ≫ s = b :=
  (originalThickened_lift f hL d V c k n a b h).choose_spec.1.2

/-- Transitivity holds on the full scheme of composable closed arrows. -/
theorem originalThickened_composable_class :
    (relativeFppfSheaf f).obj.map (pullback.fst s r ≫ r).op σ =
      (relativeFppfSheaf f).obj.map (pullback.snd s r ≫ s).op σ := by
  rw [originalThickened_class_natural f hL d V c k n (pullback.fst s r), pullback.condition]
  exact originalThickened_class_natural f hL d V c k n (pullback.snd s r)

/-- The full original closed relation is an internal scheme equivalence relation. -/
def originalThickenedEquivalence : CategoryTheory.EquivalenceRelation r s where
  right_cancellation _ _ _ h₁ h₂ := originalThickened_hom_ext f hL d V c k n h₁ h₂
  «r» := originalThickenedTestArrow f hL d V c k n (𝟙 _) (𝟙 _) rfl
  reflexivity₁ := originalThickenedTestArrow_fst f hL d V c k n _ _ _
  reflexivity₂ := originalThickenedTestArrow_snd f hL d V c k n _ _ _
  «s» := originalThickenedTestArrow f hL d V c k n s r
    (originalThickened_equal_class f hL d V c k n).symm
  symmetry₁ := originalThickenedTestArrow_fst f hL d V c k n _ _ _
  symmetry₂ := originalThickenedTestArrow_snd f hL d V c k n _ _ _
  c := PullbackCone.mk (pullback.fst s r) (pullback.snd s r) pullback.condition
  isLimit := pullbackIsPullback s r
  t := originalThickenedTestArrow f hL d V c k n (pullback.fst s r ≫ r) (pullback.snd s r ≫ s)
    (originalThickened_composable_class f hL d V c k n)
  transitivity₁ := originalThickenedTestArrow_fst f hL d V c k n _ _ _
  transitivity₂ := originalThickenedTestArrow_snd f hL d V c k n _ _ _

/-- Closed reflexivity retains the original diagonal scheme morphism. -/
@[reassoc]
theorem originalThickenedEquivalence_refl_arrow :
    (originalThickenedEquivalence f hL d V c k n).r ≫ z = i ≫ (equivalence f hL d V c k).r := by
  apply hom_ext f hL d V c k <;>
    simp only [Category.assoc, originalThickenedArrow_fst, originalThickenedArrow_snd,
      (originalThickenedEquivalence f hL d V c k n).reflexivity₁_assoc,
      (originalThickenedEquivalence f hL d V c k n).reflexivity₂_assoc,
      (equivalence f hL d V c k).reflexivity₁,
      (equivalence f hL d V c k).reflexivity₂,
      Category.comp_id]

/-- Closed symmetry retains the original inversion scheme morphism. -/
@[reassoc]
theorem originalThickenedEquivalence_swap_arrow :
    (originalThickenedEquivalence f hL d V c k n).s ≫ z = z ≫ (equivalence f hL d V c k).s := by
  apply hom_ext f hL d V c k <;>
    simp only [Category.assoc, originalThickenedArrow_fst, originalThickenedArrow_snd,
      (originalThickenedEquivalence f hL d V c k n).symmetry₁_assoc,
      (originalThickenedEquivalence f hL d V c k n).symmetry₂_assoc,
      (equivalence f hL d V c k).symmetry₁,
      (equivalence f hL d V c k).symmetry₂]

end FLT.Mazur.HilbertChart.AffineRestriction
