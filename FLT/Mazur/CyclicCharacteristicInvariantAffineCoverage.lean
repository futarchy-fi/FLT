/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicInvariantAffineCover
public import FLT.Mazur.CyclicCharacteristicNormalizedSubgroup
public import FLT.Mazur.CompatibleSubgroupBaseChangeCompEq

/-!
# Actual smooth subgroup coverage by the invariant affine charts

Refine the original normalized fppf cover through the constructed finite
invariant affine target cover. The comparison retains the full original curve
and subgroup scheme, including non-etale cyclic subgroups on arbitrary bases.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n]

/-- The actual full curve on each selected invariant affine chart. -/
def invariantAffineCurve (i : InvariantAffineIndex n) :
    GeneralizedEllipticCurve (invariantAffineChart n i) :=
  (normalizedCurve n i.1).baseChange (invariantAffineInclusion n i)

/-- The actual full subgroup on each selected invariant affine chart. -/
def invariantAffineSubgroup (i : InvariantAffineIndex n) :
    (invariantAffineCurve n i).FiniteSubgroup n :=
  (normalizedSubgroup n i.1).baseChange (invariantAffineInclusion n i)

/-- The selected invariant chart retains cyclicity of the universal subgroup. -/
theorem invariantAffineSubgroup_isCyclic (i : InvariantAffineIndex n) :
    (invariantAffineSubgroup n i).IsCyclic :=
  (normalizedSubgroup_isCyclic n i.1).baseChange _ _

/-- The selected invariant chart retains ampleness of the universal subgroup. -/
theorem invariantAffineSubgroup_isAmple (i : InvariantAffineIndex n) :
    (invariantAffineSubgroup n i).IsAmple :=
  (normalizedSubgroup_isAmple n i.1).baseChange _

variable {S : Scheme} {E : GeneralizedEllipticCurve S} [Smooth E.curve.hom]
  (H : E.FiniteSubgroup n) (hc : H.IsCyclic) (ha : H.IsAmple)

include hc ha in
/-- Every original point admits a flat local parameter in an actual invariant affine chart. -/
theorem exists_invariantAffine_neighborhood (x : S) :
    ∃ (U : Scheme) (g : U ⟶ S), Flat g ∧ LocallyOfFinitePresentation g ∧
      x ∈ Set.range g ∧ ∃ (i : InvariantAffineIndex n) (q : U ⟶ invariantAffineChart n i),
        Nonempty (CompatibleIso ((invariantAffineSubgroup n i).baseChange q)
          (H.baseChange g)) := by
  obtain ⟨C, b, v, hv⟩ := exists_normalized_subgroup_fppf_cover n H hc ha
  let D : S.Cover (Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation)) := C
  obtain ⟨i, y, hy⟩ := D.exists_eq x
  let _ : Flat (C.f i) := (D.map_prop i).1
  let _ : LocallyOfFinitePresentation (C.f i) := (D.map_prop i).2
  obtain ⟨j, z, hz⟩ := (invariantAffineCover n (b i)).exists_eq (v i y)
  let k : InvariantAffineIndex n := ⟨b i, j⟩
  let p := pullback.fst (v i) (invariantAffineInclusion n k)
  let q := pullback.snd (v i) (invariantAffineInclusion n k)
  have hp : y ∈ Set.range p := by
    rw [Scheme.Pullback.range_fst]
    exact ⟨z, hz⟩
  obtain ⟨w, hw⟩ := hp
  obtain ⟨a⟩ := hv i
  refine ⟨pullback (v i) (invariantAffineInclusion n k), p ≫ C.f i,
    inferInstance, inferInstance, ⟨w, ?_⟩, k, q, ⟨?_⟩⟩
  · change C.f i (p w) = x
    rw [hw]
    exact hy
  · exact (compatibleBaseChangeComp (normalizedSubgroup n (b i))
      (invariantAffineInclusion n k) q).symm.trans
      ((compatibleBaseChangeCompEq (normalizedSubgroup n (b i)) (v i) p
        (q ≫ invariantAffineInclusion n k) pullback.condition.symm).trans
        ((a.baseChange p).trans (compatibleBaseChangeComp H (C.f i) p).symm))

include hc ha in
/-- The finite invariant affine target family covers every original smooth cyclic object fppf. -/
theorem exists_invariantAffine_subgroup_fppf_cover :
    ∃ (C : Scheme.Cover.{0} Scheme.fppfPrecoverage S)
      (i : C.I₀ → InvariantAffineIndex n)
      (q : ∀ a : C.I₀, C.X a ⟶ invariantAffineChart n (i a)),
      ∀ a, Nonempty (CompatibleIso ((invariantAffineSubgroup n (i a)).baseChange (q a))
        (H.baseChange (C.f a))) := by
  choose U g hg hl hx i q hq using exists_invariantAffine_neighborhood n H hc ha
  let C : Scheme.Cover.{0} Scheme.fppfPrecoverage S :=
    Scheme.Cover.mkOfCovers (P := @Flat ⊓ @LocallyOfFinitePresentation) S U g
      (fun x => ⟨x, hx x⟩) (fun x => ⟨hg x, hl x⟩)
  exact ⟨C, i, q, hq⟩

end FLT.Mazur.CyclicCharacteristicAtlas
