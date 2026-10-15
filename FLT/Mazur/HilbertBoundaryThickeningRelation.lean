/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertBoundarySchemeTests
public import FLT.Mazur.InvariantIdealRelation
public import FLT.Mazur.AffineIdealPowerPullback

/-!
# The full relation on every infinitesimal boundary neighborhood

Each positive power of the original boundary ideal defines an affine closed
scheme over the unchanged coefficient base. Exact power invariance constructs
both original endpoints on the whole relation, retaining transverse nilpotents.
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
local notation "I" => boundaryIdealSheaf π O ^ (n + 1)

/-- The full infinitesimal source over the unchanged original coefficient base. -/
def originalThickenedSource : Over (Spec (.of R)) := Over.mk ((I).subschemeι ≫ A.hom)

/-- Its whole original source map retains the nilpotent thickening. -/
def originalThickenedSourceMap : originalThickenedSource f hL d V c k n ⟶ A :=
  Over.homMk (I).subschemeι

local notation "B" => originalThickenedSource f hL d V c k n
local notation "i" => originalThickenedSourceMap f hL d V c k n
local notation "D" => relation f hL d V c k
local notation "p" => fst f hL d V c k
local notation "q" => snd f hL d V c k

/-- The boundary inclusion is an actual closed immersion. -/
instance originalThickenedSourceMap_closed : IsClosedImmersion (i).left := by
  change IsClosedImmersion (I).subschemeι
  infer_instance

/-- Closed boundary maps are monomorphisms over the original coefficient base. -/
instance originalThickenedSourceMap_mono : Mono i := Over.mono_of_mono_left _

/-- The closed boundary is affine, with its full equation ideal. -/
instance originalThickenedSource_affine : IsAffine (B).left :=
  isAffine_of_isAffineHom (i).left

/-- The whole original relation restricted at its first closed endpoint. -/
def originalThickenedRelation : Over (Spec (.of R)) :=
  Over.mk (pullback.fst (p).left (i).left ≫ (D).hom)

/-- The closed relation retains its complete original relation arrow. -/
def originalThickenedArrow : originalThickenedRelation f hL d V c k n ⟶ D :=
  Over.homMk (pullback.fst (p).left (i).left)

/-- Its first endpoint lies in the actual closed scheme. -/
def originalThickenedFst : originalThickenedRelation f hL d V c k n ⟶ B :=
  Over.homMk (pullback.snd (p).left (i).left) (by
    change pullback.snd (p).left (i).left ≫ (i).left ≫ A.hom = _
    rw [← Category.assoc, ← pullback.condition, Category.assoc, Over.w p]
    rfl)

/-- Its second endpoint is constructed from exact ideal-sheaf invariance. -/
def originalThickenedSnd : originalThickenedRelation f hL d V c k n ⟶ B := by
  let _ := selectedHilbertSource_isLocallyNoetherian f d V k
  refine Over.homMk (InvariantIdealRelation.snd I (p).left (q).left
    (AffineIdealPower.comap_pow_eq _ _ _
      (boundaryIdealSheaf_comap_eq π O (p).left (q).left
        (fullEnvelopeInterior_invariant f hL d V c k)) (n + 1))) ?_
  change _ ≫ (I).subschemeι ≫ A.hom = _
  rw [← Category.assoc, InvariantIdealRelation.snd_ι, Category.assoc, Over.w q]
  rfl

omit [Etale V.hom] [IsAffine A.left] in
/-- The first endpoint keeps its original source map. -/
@[reassoc]
theorem originalThickenedArrow_fst :
    originalThickenedArrow f hL d V c k n ≫ p = originalThickenedFst f hL d V c k n ≫ i := by
  apply Over.OverMorphism.ext
  exact pullback.condition

/-- The second endpoint keeps its independent original source map. -/
@[reassoc]
theorem originalThickenedArrow_snd :
    originalThickenedArrow f hL d V c k n ≫ q = originalThickenedSnd f hL d V c k n ≫ i := by
  let _ := selectedHilbertSource_isLocallyNoetherian f d V k
  apply Over.OverMorphism.ext
  exact (InvariantIdealRelation.snd_ι I (p).left (q).left
    (AffineIdealPower.comap_pow_eq _ _ _
      (boundaryIdealSheaf_comap_eq π O (p).left (q).left
        (fullEnvelopeInterior_invariant f hL d V c k)) (n + 1))).symm

/-- The original Picard section restricted to the whole closed source. -/
def originalThickenedSection : (relativeFppfSheaf f).obj.obj (op B) :=
  (relativeFppfSheaf f).obj.map (i).op (sectionAt f hL d V c k)

/-- The full closed endpoints give the same original Picard class. -/
theorem originalThickened_equal_class :
    (relativeFppfSheaf f).obj.map (originalThickenedFst f hL d V c k n).op
      (originalThickenedSection f hL d V c k n) =
    (relativeFppfSheaf f).obj.map (originalThickenedSnd f hL d V c k n).op
      (originalThickenedSection f hL d V c k n) := by
  dsimp only [originalThickenedSection]
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
    ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
    ← originalThickenedArrow_fst, ← originalThickenedArrow_snd]
  exact equal_class_natural f hL d V c k _

/-- The closed restriction forgets no original relation arrow. -/
instance originalThickenedArrow_mono : Mono (originalThickenedArrow f hL d V c k n) := by
  let _ : Mono (originalThickenedArrow f hL d V c k n).left := by
    change Mono (pullback.fst (p).left (i).left)
    infer_instance
  exact Over.mono_of_mono_left _

/-- Both closed endpoints distinguish all maps, including nonreduced tests. -/
theorem originalThickened_hom_ext {T : Over (Spec (.of R))}
    {a b : T ⟶ originalThickenedRelation f hL d V c k n}
    (h₁ : a ≫ originalThickenedFst f hL d V c k n = b ≫ originalThickenedFst f hL d V c k n)
    (h₂ : a ≫ originalThickenedSnd f hL d V c k n = b ≫ originalThickenedSnd f hL d V c k n) :
    a = b := by
  apply (cancel_mono (originalThickenedArrow f hL d V c k n)).mp
  apply hom_ext f hL d V c k
  · rw [Category.assoc, Category.assoc, originalThickenedArrow_fst, ← Category.assoc,
      ← Category.assoc, h₁]
  · rw [Category.assoc, Category.assoc, originalThickenedArrow_snd, ← Category.assoc,
      ← Category.assoc, h₂]

end FLT.Mazur.HilbertChart.AffineRestriction
