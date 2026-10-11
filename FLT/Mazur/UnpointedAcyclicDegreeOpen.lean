/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AcyclicDivisorDegreeOpen
public import FLT.Mazur.UnpointedAcyclicOpenDivisor
public import FLT.Mazur.AcyclicDegreePicardRepresentation

/-!
# Open constant-degree charts of arbitrary original Picard sections

The canonical full divisor on the unpointed acyclic test open has actual
constant-degree strata. Their composite inclusions are open immersions into
the original test. Each represents the degree-d Picard subfunctor on that test.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite TopologicalSpace
namespace FLT.Mazur.CartierAbel
open FCurve SchemePicard
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X : Scheme} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f]
  (T : Over (Spec (.of R))) (s : (relativeFppfSheaf f).obj.obj (op T)) (d : ℕ)

/-- The degree stratum inside the actual acyclic open of an arbitrary Picard section. -/
def unpointedAcyclicDegreeTest : Over (Spec (.of R)) :=
  acyclicDivisorDegreeTest f (finiteTypeUnpointedFppfOpenTest f T s)
    (finiteTypeUnpointedOpenDivisor f T s) d

/-- Its original inclusion into the acyclic test open. -/
def unpointedAcyclicDegreeToAcyclic :
    unpointedAcyclicDegreeTest f T s d ⟶ finiteTypeUnpointedFppfOpenTest f T s :=
  acyclicDivisorDegreeArrow f _ (finiteTypeUnpointedOpenDivisor f T s) d

/-- Its composite inclusion into the original Picard test scheme. -/
def unpointedAcyclicDegreeArrow : unpointedAcyclicDegreeTest f T s d ⟶ T :=
  unpointedAcyclicDegreeToAcyclic f T s d ≫ finiteTypeUnpointedFppfOpenArrow f T s

instance unpointedAcyclicDegreeArrow_isOpenImmersion :
    IsOpenImmersion (unpointedAcyclicDegreeArrow f T s d).left := by
  dsimp [unpointedAcyclicDegreeArrow, unpointedAcyclicDegreeToAcyclic,
    acyclicDivisorDegreeArrow, finiteTypeUnpointedFppfOpenArrow]
  infer_instance

instance unpointedAcyclicDegreeArrow_mono : Mono (unpointedAcyclicDegreeArrow f T s d) :=
  Over.mono_of_mono_left _

/-- The exact range of the new chart as an open of the original test. -/
def unpointedAcyclicDegreeOpen : T.left.Opens :=
  (unpointedAcyclicDegreeArrow f T s d).left.opensRange

/-- Every actual degree-d chart restricts the original section to a degree-d full divisor. -/
theorem unpointedAcyclicDegreeArrow_mem :
    (relativeFppfSheaf f).obj.map (unpointedAcyclicDegreeArrow f T s d).op s ∈
      (acyclicDegreePicardSubfunctor f d).obj (op (unpointedAcyclicDegreeTest f T s d)) := by
  let k := unpointedAcyclicDegreeToAcyclic f T s d
  refine ⟨⟨finiteTypeAcyclicDivisorMap f k (finiteTypeUnpointedOpenDivisor f T s),
    acyclicDivisorDegreeArrow_mem f _ _ d⟩, ?_⟩
  exact finiteTypeUnpointedOpenDivisor_map_class f T s k

/-- Every constant-degree acyclic restriction factors through the actual degree chart. -/
theorem unpointedAcyclicDegreeOpen_represents {U : Over (Spec (.of R))} (b : U ⟶ T) :
    (relativeFppfSheaf f).obj.map b.op s ∈ (acyclicDegreePicardSubfunctor f d).obj (op U) ↔
      ∃! k : U ⟶ unpointedAcyclicDegreeTest f T s d,
        k ≫ unpointedAcyclicDegreeArrow f T s d = b := by
  constructor
  · intro hb
    obtain ⟨k, hk, _⟩ := (finiteTypeUnpointedFppfAcyclicOpen_represents_over f b s).mp
      (acyclicDegreePicard_le_local f d _ hb)
    obtain ⟨D, hD⟩ := hb
    have he : D.val = finiteTypeAcyclicDivisorMap f k
        (finiteTypeUnpointedOpenDivisor f T s) := by
      apply finiteTypeUnpointedOpenDivisor_unique f T s k
      rw [hk]
      exact hD
    have hd : finiteTypeAcyclicDivisorMap f k (finiteTypeUnpointedOpenDivisor f T s) ∈
        (acyclicDivisorDegreeSubfunctor f d).obj (op U) := he ▸ D.property
    obtain ⟨l, hl, _⟩ := (acyclicDivisorDegreeOpen_represents f _ _ k d).mp hd
    refine ⟨l, ?_, fun m hm ↦ (cancel_mono (unpointedAcyclicDegreeArrow f T s d)).mp ?_⟩
    · change l ≫ (acyclicDivisorDegreeArrow f _ _ d ≫ _) = b
      rw [← Category.assoc, hl, hk]
    · exact hm.trans (by
        change b = l ≫ (acyclicDivisorDegreeArrow f _ _ d ≫ _)
        rw [← Category.assoc, hl, hk])
  · rintro ⟨k, hk, _⟩
    have h := (acyclicDegreePicardSubfunctor f d).map k.op
      (unpointedAcyclicDegreeArrow_mem f T s d)
    change (relativeFppfSheaf f).obj.map k.op
      ((relativeFppfSheaf f).obj.map (unpointedAcyclicDegreeArrow f T s d).op s) ∈
        (acyclicDegreePicardSubfunctor f d).obj (op U) at h
    simpa only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, hk] using h

/-- The constant-degree charts exhaust the original acyclic test open. -/
theorem iSup_unpointedAcyclicDegreeOpen :
    ⨆ d, unpointedAcyclicDegreeOpen f T s d = finiteTypeUnpointedFppfAcyclicOpen f T s := by
  apply le_antisymm
  · apply iSup_le
    intro d t ht
    obtain ⟨u, rfl⟩ := ht
    exact ((unpointedAcyclicDegreeToAcyclic f T s d).left u).property
  · intro t ht
    let u : (finiteTypeUnpointedFppfOpenTest f T s).left := ⟨t, ht⟩
    let D := finiteTypeUnpointedOpenDivisor f T s
    let d := (acyclicDivisorProjection f _ D).finrank u
    apply Opens.mem_iSup.mpr
    refine ⟨d, ?_⟩
    exact ⟨⟨u, show u ∈ acyclicDivisorDegreeOpen f _ D d from rfl⟩, rfl⟩

end FLT.Mazur.CartierAbel
