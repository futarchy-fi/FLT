/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AcyclicDivisorFixedBaseChange
public import FLT.Mazur.AcyclicDivisorDegreePresheaf

/-!
# Degree and naturality of fixed-base acyclic divisor transport

The full-divisor equivalence preserves finite locally free degree in both
directions. Its naturality is equality of the entire pulled-back ideal, so
it compares the actual degree-d Hilbert functors on arbitrary new-base tests.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.CartierAbel
open FCurve SchemePicard
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R R' : Type} [CommRing R] [CommRing R']
  [Algebra.FiniteType ℤ R] [Algebra.FiniteType ℤ R']
  {X : Scheme} (f : X ⟶ Spec (.of R)) (a : Spec (.of R') ⟶ Spec (.of R))
  [IsProper f] [Flat f] [GeometricallyIntegral f]
local notation "q" => Limits.pullback.snd f a

/-- The new model and original model give the same degree to the transported full divisor. -/
theorem acyclicDivisorFixedBaseChange_degree_iff (T : Over (Spec (.of R')))
    (D : AcyclicRankOneRelativeDivisor (Limits.pullback.snd f ((Over.map a).obj T).hom))
    (d : ℕ) :
    FiniteLocallyFreeDegree
        ((acyclicDivisorFixedBaseChange f a T D).val.val.subschemeι ≫
          Limits.pullback.snd q T.hom) d ↔
      FiniteLocallyFreeDegree (D.val.val.subschemeι ≫
        Limits.pullback.snd f ((Over.map a).obj T).hom) d := by
  constructor
  · intro hd
    have hh := finiteTypeAcyclicDivisorCartesianMap_degree
      (IsPullback.of_hasPullback q T.hom)
      (IsPullback.of_hasPullback f ((Over.map a).obj T).hom)
      (fixedBaseTotal_inv_isPullback f a T) (acyclicDivisorFixedBaseChange f a T D) d hd
    have he : acyclicDivisorFixedBaseChangeInv f a T
        (acyclicDivisorFixedBaseChange f a T D) = D :=
      (acyclicDivisorFixedBaseEquiv f a T).left_inv D
    change FiniteLocallyFreeDegree
      ((acyclicDivisorFixedBaseChangeInv f a T
        (acyclicDivisorFixedBaseChange f a T D)).val.val.subschemeι ≫ _) d at hh
    rwa [he] at hh
  · exact finiteTypeAcyclicDivisorCartesianMap_degree _ _ _ D d

/-- The full fixed-base equivalence restricts to exactly the degree-d divisor functor. -/
def acyclicDegreeFixedBaseEquiv (d : ℕ) (T : Over (Spec (.of R'))) :
    (acyclicDivisorDegreeSubfunctor f d).toFunctor.obj (op ((Over.map a).obj T)) ≃
      (acyclicDivisorDegreeSubfunctor q d).toFunctor.obj (op T) :=
  (acyclicDivisorFixedBaseEquiv f a T).subtypeEquiv
    (fun D ↦ (acyclicDivisorFixedBaseChange_degree_iff f a T D d).symm)

/-- Full-divisor transport commutes with every map between tests over the new base. -/
theorem acyclicDivisorFixedBaseChange_natural {T U : Over (Spec (.of R'))} (k : T ⟶ U)
    (D : AcyclicRankOneRelativeDivisor (Limits.pullback.snd f ((Over.map a).obj U).hom)) :
    acyclicDivisorFixedBaseChange f a T (finiteTypeAcyclicDivisorMap f ((Over.map a).map k) D) =
      finiteTypeAcyclicDivisorMap q k (acyclicDivisorFixedBaseChange f a U D) := by
  apply acyclicRankOneRelativeDivisor_ext
  rw [acyclicDivisorFixedBaseChange_ideal, finiteTypeAcyclicDivisorMap_ideal,
    finiteTypeAcyclicDivisorMap_ideal, acyclicDivisorFixedBaseChange_ideal,
    ← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
    relativeBaseChangeTotalIso_naturality]

/-- The degree-d Hilbert divisor functors agree naturally after coefficient base change. -/
def acyclicDegreeFixedBaseIso (d : ℕ) :
    (Over.map a).op ⋙ (acyclicDivisorDegreeSubfunctor f d).toFunctor ≅
      (acyclicDivisorDegreeSubfunctor q d).toFunctor :=
  NatIso.ofComponents (fun T ↦ (acyclicDegreeFixedBaseEquiv f a d T.unop).toIso)
    (fun {T U} k ↦ by
      apply ConcreteCategory.hom_ext
      intro D
      apply Subtype.ext
      exact acyclicDivisorFixedBaseChange_natural f a k.unop D.val)

end FLT.Mazur.CartierAbel
