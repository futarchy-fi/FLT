/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertBoundarySchemeTests
public import FLT.Mazur.EnvelopeBoundaryRelation

/-!
# The full original closed Hilbert relation

The closed boundary carries both original endpoints, over the unchanged
coefficient base. Its relation scheme is the first endpoint pullback of the
whole original relation; exact ideal invariance supplies the second endpoint.
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
local notation "B" => originalBoundarySource f hL d V c k
local notation "i" => originalBoundarySourceMap f hL d V c k
local notation "D" => relation f hL d V c k
local notation "p" => fst f hL d V c k
local notation "q" => snd f hL d V c k

/-- The boundary inclusion is an actual closed immersion. -/
instance originalBoundarySourceMap_closed : IsClosedImmersion (i).left := by
  change IsClosedImmersion (boundaryIdealSheaf π O).subschemeι
  infer_instance

/-- Closed boundary maps are monomorphisms over the original coefficient base. -/
instance originalBoundarySourceMap_mono : Mono i := Over.mono_of_mono_left _

/-- The closed boundary is affine, with its full equation ideal. -/
instance originalBoundarySource_affine : IsAffine (B).left :=
  isAffine_of_isAffineHom (i).left

/-- The whole original relation restricted at its first closed endpoint. -/
def originalClosedRelation : Over (Spec (.of R)) :=
  Over.mk (pullback.fst (p).left (i).left ≫ (D).hom)

/-- The closed relation retains its complete original relation arrow. -/
def originalClosedArrow : originalClosedRelation f hL d V c k ⟶ D :=
  Over.homMk (pullback.fst (p).left (i).left)

/-- Its first endpoint lies in the actual closed scheme. -/
def originalClosedFst : originalClosedRelation f hL d V c k ⟶ B :=
  Over.homMk (pullback.snd (p).left (i).left) (by
    change pullback.snd (p).left (i).left ≫ (i).left ≫ A.hom = _
    rw [← Category.assoc, ← pullback.condition, Category.assoc, Over.w p]
    rfl)

/-- Its second endpoint is constructed from exact ideal-sheaf invariance. -/
def originalClosedSnd : originalClosedRelation f hL d V c k ⟶ B := by
  let _ := selectedHilbertSource_isLocallyNoetherian f d V k
  refine Over.homMk (boundaryRelationSnd π O (p).left (q).left
    (fullEnvelopeInterior_invariant f hL d V c k)) ?_
  change _ ≫ (boundaryIdealSheaf π O).subschemeι ≫ A.hom = _
  rw [← Category.assoc, boundaryRelationSnd_comp, Category.assoc, Over.w q]
  rfl

omit [Etale V.hom] [IsAffine A.left] in
/-- The first endpoint keeps its original source map. -/
@[reassoc]
theorem originalClosedArrow_fst :
    originalClosedArrow f hL d V c k ≫ p = originalClosedFst f hL d V c k ≫ i := by
  apply Over.OverMorphism.ext
  exact pullback.condition

/-- The second endpoint keeps its independent original source map. -/
@[reassoc]
theorem originalClosedArrow_snd :
    originalClosedArrow f hL d V c k ≫ q = originalClosedSnd f hL d V c k ≫ i := by
  let _ := selectedHilbertSource_isLocallyNoetherian f d V k
  apply Over.OverMorphism.ext
  exact (boundaryRelationSnd_comp π O (p).left (q).left
    (fullEnvelopeInterior_invariant f hL d V c k)).symm

/-- The original Picard section restricted to the whole closed source. -/
def originalClosedSection : (relativeFppfSheaf f).obj.obj (op B) :=
  (relativeFppfSheaf f).obj.map (i).op (sectionAt f hL d V c k)

/-- The full closed endpoints give the same original Picard class. -/
theorem originalClosed_equal_class :
    (relativeFppfSheaf f).obj.map (originalClosedFst f hL d V c k).op
      (originalClosedSection f hL d V c k) =
    (relativeFppfSheaf f).obj.map (originalClosedSnd f hL d V c k).op
      (originalClosedSection f hL d V c k) := by
  dsimp only [originalClosedSection]
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
    ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
    ← originalClosedArrow_fst, ← originalClosedArrow_snd]
  exact equal_class_natural f hL d V c k _

/-- The closed restriction forgets no original relation arrow. -/
instance originalClosedArrow_mono : Mono (originalClosedArrow f hL d V c k) := by
  let _ : Mono (originalClosedArrow f hL d V c k).left := by
    change Mono (pullback.fst (p).left (i).left)
    infer_instance
  exact Over.mono_of_mono_left _

/-- Both closed endpoints distinguish all maps, including nonreduced tests. -/
theorem originalClosed_hom_ext {T : Over (Spec (.of R))}
    {a b : T ⟶ originalClosedRelation f hL d V c k}
    (h₁ : a ≫ originalClosedFst f hL d V c k = b ≫ originalClosedFst f hL d V c k)
    (h₂ : a ≫ originalClosedSnd f hL d V c k = b ≫ originalClosedSnd f hL d V c k) :
    a = b := by
  apply (cancel_mono (originalClosedArrow f hL d V c k)).mp
  apply hom_ext f hL d V c k
  · rw [Category.assoc, Category.assoc, originalClosedArrow_fst, ← Category.assoc,
      ← Category.assoc, h₁]
  · rw [Category.assoc, Category.assoc, originalClosedArrow_snd, ← Category.assoc,
      ← Category.assoc, h₂]

end FLT.Mazur.HilbertChart.AffineRestriction
