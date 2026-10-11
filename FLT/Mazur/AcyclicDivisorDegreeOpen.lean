/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeCartierCurveFinite
public import FLT.Mazur.FiniteFlatDegreeOpen
public import FLT.Mazur.AcyclicDivisorDegreePresheaf

/-!
# Degree opens of every full acyclic divisor

Each full acyclic divisor on an arbitrary original test is finite flat and
finitely presented. Its degree strata cover that test and commute with all
original test maps. Membership in the constant-degree presheaf is detected
by the image in this actual open.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.CartierAbel
open FCurve ClosedIdealCover SchemePicard
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X : Scheme} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f]
  (T : Over (Spec (.of R))) (D : AcyclicRankOneRelativeDivisor (pullback.snd f T.hom))

/-- The structure map of the actual full divisor, in the original Picard convention. -/
def acyclicDivisorProjection : D.val.val.subscheme ⟶ T.left :=
  D.val.val.subschemeι ≫ pullback.snd f T.hom

instance acyclicDivisorProjection_isFinite : IsFinite (acyclicDivisorProjection f T D) := by
  let _ : SmoothOfRelativeDimension 1 (pullback.snd f T.hom) :=
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) f T.hom inferInstance
  exact RelativeEffectiveCartier.isFinite _ ⟨D.val.property, D.property.1⟩

instance acyclicDivisorProjection_flat : Flat (acyclicDivisorProjection f T D) := D.property.1

instance acyclicDivisorProjection_presented :
    LocallyOfFinitePresentation (acyclicDivisorProjection f T D) := by
  let _ := SmoothOfRelativeDimension.smooth 1 f
  exact D.val.property.locallyOfFinitePresentation_comp _

/-- The actual constant-degree open of any acyclic full divisor. -/
def acyclicDivisorDegreeOpen (d : ℕ) : T.left.Opens :=
  finiteFlatDegreeOpen (acyclicDivisorProjection f T D) d

omit [Algebra.FiniteType ℤ R] [Flat f] in
@[simp]
lemma mem_acyclicDivisorDegreeOpen (d : ℕ) (t : T.left) :
    t ∈ acyclicDivisorDegreeOpen f T D d ↔
      (acyclicDivisorProjection f T D).finrank t = d := Iff.rfl

omit [Algebra.FiniteType ℤ R] [Flat f] in
/-- The degree opens exhaust all tests carrying an acyclic full divisor. -/
theorem iSup_acyclicDivisorDegreeOpen : ⨆ d, acyclicDivisorDegreeOpen f T D d = ⊤ :=
  iSup_finiteFlatDegreeOpen _

/-- Pullback preserves the full divisor's fiber rank along the original test map. -/
theorem acyclicDivisorProjection_finrank_map {U : Over (Spec (.of R))}
    (b : U ⟶ T) (u : U.left) :
    (acyclicDivisorProjection f U (finiteTypeAcyclicDivisorMap f b D)).finrank u =
      (acyclicDivisorProjection f T D).finrank (b.left u) := by
  let _ : Flat (D.val.val.subschemeι ≫ pullback.snd f T.hom) := D.property.1
  let _ : IsFinite (D.val.val.subschemeι ≫ pullback.snd f T.hom) :=
    acyclicDivisorProjection_isFinite f T D
  unfold acyclicDivisorProjection
  rw [finiteTypeAcyclicDivisorMap_ideal]
  exact Scheme.Hom.finrank_of_isPullback _ _ _ _
    (restrictionMap_base_isPullback D.val.val _ (relativeTotalMap_isPullback f b)) u

/-- Actual degree opens commute with all original test maps. -/
theorem acyclicDivisorDegreeOpen_map {U : Over (Spec (.of R))} (b : U ⟶ T) (d : ℕ) :
    acyclicDivisorDegreeOpen f U (finiteTypeAcyclicDivisorMap f b D) d =
      b.left ⁻¹ᵁ acyclicDivisorDegreeOpen f T D d := by
  ext u
  exact congrArg (· = d) (acyclicDivisorProjection_finrank_map f T D b u) |>.to_iff

/-- Constant degree after pullback is exactly containment in the original degree stratum. -/
theorem acyclicDivisorDegreeOpen_map_mem_iff {U : Over (Spec (.of R))}
    (b : U ⟶ T) (d : ℕ) :
    finiteTypeAcyclicDivisorMap f b D ∈ (acyclicDivisorDegreeSubfunctor f d).obj (op U) ↔
      ∀ u : U.left, b.left u ∈ acyclicDivisorDegreeOpen f T D d := by
  change FiniteLocallyFreeDegree
    (acyclicDivisorProjection f U (finiteTypeAcyclicDivisorMap f b D)) d ↔ _
  constructor
  · intro h u
    rw [mem_acyclicDivisorDegreeOpen, ← acyclicDivisorProjection_finrank_map f T D b u]
    exact h.2.2.2 u
  · intro h
    refine ⟨inferInstance, inferInstance, inferInstance, fun u ↦ ?_⟩
    rw [acyclicDivisorProjection_finrank_map]
    exact h u

/-- The degree open as an original test scheme. -/
def acyclicDivisorDegreeTest (d : ℕ) : Over (Spec (.of R)) :=
  Over.mk ((acyclicDivisorDegreeOpen f T D d).ι ≫ T.hom)

/-- The actual open inclusion in the original test category. -/
def acyclicDivisorDegreeArrow (d : ℕ) : acyclicDivisorDegreeTest f T D d ⟶ T :=
  Over.homMk (acyclicDivisorDegreeOpen f T D d).ι

/-- A degree-d divisor is uniquely represented by a map into the actual degree open. -/
theorem acyclicDivisorDegreeOpen_represents {U : Over (Spec (.of R))}
    (b : U ⟶ T) (d : ℕ) :
    finiteTypeAcyclicDivisorMap f b D ∈ (acyclicDivisorDegreeSubfunctor f d).obj (op U) ↔
      ∃! k : U ⟶ acyclicDivisorDegreeTest f T D d,
        k ≫ acyclicDivisorDegreeArrow f T D d = b := by
  rw [acyclicDivisorDegreeOpen_map_mem_iff]
  constructor
  · intro hu
    have hr : Set.range b.left ⊆ Set.range (acyclicDivisorDegreeOpen f T D d).ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨u, rfl⟩
      exact hu u
    let k := IsOpenImmersion.lift (acyclicDivisorDegreeOpen f T D d).ι b.left hr
    have hk : k ≫ (acyclicDivisorDegreeOpen f T D d).ι = b.left :=
      IsOpenImmersion.lift_fac _ _ _
    refine ⟨Over.homMk k (by
      change k ≫ (acyclicDivisorDegreeOpen f T D d).ι ≫ T.hom = U.hom
      rw [← Category.assoc, hk, Over.w]), Over.OverMorphism.ext hk, ?_⟩
    intro l hl
    apply Over.OverMorphism.ext
    apply (cancel_mono (acyclicDivisorDegreeOpen f T D d).ι).mp
    exact (congrArg Over.Hom.left hl).trans hk.symm
  · rintro ⟨k, hk, _⟩ u
    have hk' := congrArg Over.Hom.left hk
    change k.left ≫ (acyclicDivisorDegreeOpen f T D d).ι = b.left at hk'
    rw [← hk']
    exact (k.left u).property

/-- The actual restricted full divisor on its degree open has that degree. -/
theorem acyclicDivisorDegreeArrow_mem (d : ℕ) :
    finiteTypeAcyclicDivisorMap f (acyclicDivisorDegreeArrow f T D d) D ∈
      (acyclicDivisorDegreeSubfunctor f d).obj (op (acyclicDivisorDegreeTest f T D d)) := by
  apply (acyclicDivisorDegreeOpen_map_mem_iff f T D _ d).mpr
  exact fun u ↦ u.property

end FLT.Mazur.CartierAbel
