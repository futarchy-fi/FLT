/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertBoundaryClosedRelation

/-!
# Cartesian closed endpoints and whole original arrows

Both closed endpoints are etale by actual base change. Every original arrow
whose first endpoint factors through the closed scheme has a canonical lift;
any specified second closed endpoint is retained automatically.
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

local notation "C" => originalClosedRelation f hL d V c k
local notation "r" => originalClosedFst f hL d V c k
local notation "s" => originalClosedSnd f hL d V c k
local notation "z" => originalClosedArrow f hL d V c k

omit [Etale V.hom] [IsAffine A.left] in
/-- The closed first endpoint is the original endpoint's exact scheme base change. -/
theorem originalClosedFst_isPullback : IsPullback (z).left (r).left (p).left (i).left :=
  IsPullback.of_hasPullback _ _

/-- The closed second endpoint is also the original endpoint's exact scheme base change. -/
theorem originalClosedSnd_isPullback : IsPullback (z).left (s).left (q).left (i).left := by
  let _ := selectedHilbertSource_isLocallyNoetherian f d V k
  exact boundaryRelationSnd_isPullback π O (p).left (q).left
    (fullEnvelopeInterior_invariant f hL d V c k)

/-- No etale arrow is lost at the closed first endpoint. -/
instance originalClosedFst_etale : Etale (r).left :=
  MorphismProperty.of_isPullback (originalClosedFst_isPullback f hL d V c k)
    (inferInstanceAs (Etale (p).left))

/-- The independent closed second endpoint is etale as well. -/
instance originalClosedSnd_etale : Etale (s).left :=
  MorphismProperty.of_isPullback (originalClosedSnd_isPullback f hL d V c k)
    (inferInstanceAs (Etale (q).left))

omit [Etale V.hom] [IsAffine A.left] in
/-- The first Cartesian square also retains the original coefficient morphisms. -/
theorem originalClosedFst_relativePullback : IsPullback z r p i :=
  IsPullback.of_map_of_faithful (Over.forget _)
    (originalClosedFst_isPullback f hL d V c k)

attribute [local irreducible] originalClosedRelation originalClosedFst originalClosedArrow
  originalBoundarySource originalBoundarySourceMap

variable {T : Over (Spec (.of R))}

/-- Lift a whole original arrow using only its first closed endpoint. -/
def originalClosedLift (a : T ⟶ D) (x : T ⟶ B) (hx : a ≫ p = x ≫ i) : T ⟶ C :=
  (originalClosedFst_relativePullback f hL d V c k).lift a x hx

omit [Etale V.hom] [IsAffine A.left] in
/-- The lift preserves the entire original relation arrow. -/
@[reassoc]
theorem originalClosedLift_arrow (a : T ⟶ D) (x : T ⟶ B)
    (hx : a ≫ p = x ≫ i) : originalClosedLift f hL d V c k a x hx ≫ z = a := by
  exact (originalClosedFst_relativePullback f hL d V c k).lift_fst a x hx

omit [Etale V.hom] [IsAffine A.left] in
/-- The lifted first endpoint is the supplied whole closed map. -/
@[reassoc]
theorem originalClosedLift_fst (a : T ⟶ D) (x : T ⟶ B)
    (hx : a ≫ p = x ≫ i) : originalClosedLift f hL d V c k a x hx ≫ r = x := by
  exact (originalClosedFst_relativePullback f hL d V c k).lift_snd a x hx

/-- A given second closed endpoint is retained without any further choice. -/
@[reassoc]
theorem originalClosedLift_snd (a : T ⟶ D) (x : T ⟶ B)
    (hx : a ≫ p = x ≫ i) (y : T ⟶ B) (hy : a ≫ q = y ≫ i) :
    originalClosedLift f hL d V c k a x hx ≫ s = y := by
  apply (cancel_mono i).mp
  rw [Category.assoc, ← originalClosedArrow_snd, ← Category.assoc,
    originalClosedLift_arrow, hy]

omit [Etale V.hom] [IsAffine A.left] in
/-- The original arrow determines its closed lift uniquely. -/
theorem originalClosedLift_unique (a : T ⟶ D) (x : T ⟶ B)
    (hx : a ≫ p = x ≫ i) (w : T ⟶ C) (hw : w ≫ z = a) :
    w = originalClosedLift f hL d V c k a x hx := by
  apply (cancel_mono z).mp
  rw [hw, originalClosedLift_arrow]

/-- Equal original Picard classes give a unique closed relation arrow on every test. -/
theorem originalClosed_lift (x y : T ⟶ B)
    (hc : (relativeFppfSheaf f).obj.map x.op (originalClosedSection f hL d V c k) =
      (relativeFppfSheaf f).obj.map y.op (originalClosedSection f hL d V c k)) :
    ∃! w : T ⟶ C, w ≫ r = x ∧ w ≫ s = y := by
  have hc' : (relativeFppfSheaf f).obj.map (x ≫ i).op (sectionAt f hL d V c k) =
      (relativeFppfSheaf f).obj.map (y ≫ i).op (sectionAt f hL d V c k) := by
    simpa only [originalClosedSection, op_comp, Functor.map_comp,
      ConcreteCategory.comp_apply] using hc
  let a' := arrow f hL d V c k (x ≫ i) (y ≫ i) hc'
  have h₁ : a' ≫ p = x ≫ i := arrow_fst f hL d V c k _ _ _
  have h₂ : a' ≫ q = y ≫ i := arrow_snd f hL d V c k _ _ _
  refine ⟨originalClosedLift f hL d V c k a' x h₁,
    ⟨originalClosedLift_fst f hL d V c k _ _ _,
      originalClosedLift_snd f hL d V c k _ _ _ y h₂⟩, ?_⟩
  intro w hw
  apply originalClosed_hom_ext f hL d V c k
  · exact hw.1.trans (originalClosedLift_fst f hL d V c k _ _ _).symm
  · exact hw.2.trans (originalClosedLift_snd f hL d V c k _ _ _ y h₂).symm

end FLT.Mazur.HilbertChart.AffineRestriction
