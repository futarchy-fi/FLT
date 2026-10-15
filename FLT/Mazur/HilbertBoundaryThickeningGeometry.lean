/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertBoundaryThickeningTower

/-!
# Exact equations and topology of infinitesimal Hilbert boundaries

The kernel of each source inclusion is the actual power of the original
boundary ideal. All positive orders have the same closed support, while their
scheme structures retain the powered equations. The zeroth order recovers the
previously constructed original closed source.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve SchemeOpenEnvelope
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] boundaryIdealSheaf
/-- Equality of full ideals identifies their actual closed inclusions. -/
theorem thickenedIdealEq_subscheme_ι {Z : Scheme} (J K : Z.IdealSheafData) (h : J = K) :
    (eqToIso (congrArg Scheme.IdealSheafData.subscheme h)).hom ≫ K.subschemeι = J.subschemeι := by
  subst h
  simp

variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
local notation "π" => Over.Hom.left (prod.fst : prod A V ⟶ A)
local notation "O" => Scheme.Hom.opensRange (Over.Hom.left (toEnvelope f hL d V c k))
local notation "I" => boundaryIdealSheaf π O
local notation "B" n:max => originalThickenedSource f hL d V c k n
local notation "i" n:max => originalThickenedSourceMap f hL d V c k n
local notation "C" n:max => originalThickenedRelation f hL d V c k n
local notation "r" n:max => originalThickenedFst f hL d V c k n
local notation "s" n:max => originalThickenedSnd f hL d V c k n
local notation "z" n:max => originalThickenedArrow f hL d V c k n

omit [Etale V.hom] [IsAffine A.left] in
/-- The scheme inclusion has exactly the powered original equation ideal. -/
theorem originalThickenedSourceMap_ker (n : ℕ) : (i n).left.ker = I ^ (n + 1) :=
  Scheme.IdealSheafData.ker_subschemeι _

omit [Etale V.hom] in
/-- Its global equations retain the full power, rather than only its radical. -/
theorem originalThickenedSourceMap_ideal (n : ℕ) :
    ((i n).left.ker).ideal ⟨⊤, isAffineOpen_top A.left⟩ =
      denominatorIdeal (π).appTop.hom O ^ (n + 1) := by
  rw [originalThickenedSourceMap_ker, Scheme.IdealSheafData.ideal_pow,
    Pi.pow_apply, boundaryIdealSheaf_top]

omit [Etale V.hom] [IsAffine A.left] in
/-- Every positive order has the original closed boundary support. -/
theorem originalThickenedSourceMap_range (n : ℕ) :
    Set.range (i n).left = (I).support := by
  change Set.range (I ^ (n + 1)).subschemeι = _
  rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.support_pow_succ]

omit [Etale V.hom] in
/-- Thickening retains precisely the original excluded image closure on carriers. -/
theorem originalThickenedSourceMap_boundary (n : ℕ) :
    Set.range (i n).left = closure (π '' (O : Set _)ᶜ) := by
  rw [originalThickenedSourceMap_range, boundaryIdealSheaf_support]

/-- Each transition is a genuine closed immersion of schemes. -/
instance originalThickenedTransition_closed {m n : ℕ} (h : m ≤ n) :
    IsClosedImmersion (originalThickenedTransition f hL d V c k h).left := by
  have he := congrArg Over.Hom.left (originalThickenedTransition_source f hL d V c k h)
  change (originalThickenedTransition f hL d V c k h).left ≫ (i n).left = (i m).left at he
  let _ : IsClosedImmersion
      ((originalThickenedTransition f hL d V c k h).left ≫ (i n).left) := by
    rw [he]
    infer_instance
  exact IsClosedImmersion.of_comp_isClosedImmersion _ (i n).left

omit [Etale V.hom] [IsAffine A.left] in
/-- Every infinitesimal transition is surjective on points. -/
theorem originalThickenedTransition_surjective {m n : ℕ} (h : m ≤ n) :
    Function.Surjective (originalThickenedTransition f hL d V c k h).left := by
  intro y
  have hy : (i n).left y ∈ Set.range (i m).left := by
    rw [originalThickenedSourceMap_range, ← originalThickenedSourceMap_range f hL d V c k n]
    exact ⟨y, rfl⟩
  obtain ⟨x, hx⟩ := hy
  refine ⟨x, (i n).left.isClosedEmbedding.injective ?_⟩
  have he := congrArg (fun v : B m ⟶ A ↦ v.left x)
    (originalThickenedTransition_source f hL d V c k h)
  exact he.trans hx

omit [Etale V.hom] [IsAffine A.left] in
/-- The source tower changes infinitesimal structure without changing its topology. -/
theorem originalThickenedTransition_isHomeomorph {m n : ℕ} (h : m ≤ n) :
    IsHomeomorph (originalThickenedTransition f hL d V c k h).left :=
  isHomeomorph_iff_isEmbedding_surjective.mpr
    ⟨(originalThickenedTransition f hL d V c k h).left.isClosedEmbedding.isEmbedding,
      originalThickenedTransition_surjective f hL d V c k h⟩

omit [Etale V.hom] [IsAffine A.left] in
/-- Order zero is the full original closed boundary over its unchanged coefficient base. -/
theorem originalThickenedSource_zero :
    B 0 = originalBoundarySource f hL d V c k := by
  exact congrArg (fun J : A.left.IdealSheafData ↦ Over.mk (J.subschemeι ≫ A.hom)) (pow_one I)

/-- The order-zero comparison is an actual relative scheme isomorphism. -/
def originalThickenedSourceZeroIso : B 0 ≅ originalBoundarySource f hL d V c k := by
  refine Over.isoMk (eqToIso (congrArg Scheme.IdealSheafData.subscheme (pow_one I))) ?_
  change (eqToIso (congrArg Scheme.IdealSheafData.subscheme (pow_one I))).hom ≫
    ((I).subschemeι ≫ A.hom) = _
  rw [← Category.assoc, thickenedIdealEq_subscheme_ι (I ^ 1) I (pow_one I)]
  rfl

omit [Etale V.hom] [IsAffine A.left] in
/-- The order-zero isomorphism retains the original boundary inclusion. -/
@[reassoc]
theorem originalThickenedSourceZeroIso_source :
    (originalThickenedSourceZeroIso f hL d V c k).hom ≫
      originalBoundarySourceMap f hL d V c k = i 0 := by
  apply Over.OverMorphism.ext
  dsimp only [originalThickenedSourceZeroIso, Over.comp_left, Over.isoMk_hom_left,
    originalBoundarySourceMap, originalThickenedSourceMap, Over.homMk_left]
  exact thickenedIdealEq_subscheme_ι (I ^ (0 + 1)) I (pow_one I)

end FLT.Mazur.HilbertChart.AffineRestriction
