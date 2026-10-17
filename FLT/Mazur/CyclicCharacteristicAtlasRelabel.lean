/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicAtlasModuli
public import FLT.Mazur.CyclicHomLocusRelabelAction
public import FLT.Mazur.OddWeierstrassCyclicHomLocusRelabelAction

/-!
# One finite relabeling group on both actual characteristic charts

Independent level-four and level-three permutations, together with the cyclic
permutation, act on the two original subgroup loci. Both actions preserve the
actual universal modular class after every test-scheme pullback.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
open UniversalWeierstrass (Labels)
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n]

/-- Both auxiliary choices and the cyclic labels have independent finite relabelings. -/
abbrev RelabelGroup :=
  MulAut (Labels 4) × MulAut (Labels 3) × MulAut (Multiplicative (ZMod n))

/-- Projection to the labels used on the chart retaining characteristic three. -/
def evenLabels : RelabelGroup n →*
    (MulAut (Labels 4) × MulAut (Multiplicative (ZMod n))) where
  toFun e := (e.1, e.2.2)
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The common finite group acts on each actual closed subgroup locus. -/
def relabelAction : (b : Bool) → RelabelGroup n →* Aut (locus n b)
  | false => (UniversalWeierstrass.cyclicHomLocusRelabelAction n).comp (evenLabels n)
  | true => (OddWeierstrassParameter.cyclicHomLocusRelabelAction n).comp
      (MonoidHom.snd _ _)

/-- The acting group is finite, including when cyclic labels collide. -/
instance relabelGroup_finite : Finite (RelabelGroup n) := inferInstance

/-- On the even chart, the original universal modular object is retained exactly. -/
theorem moduliClass_even : moduliClass n false =
    UniversalWeierstrass.cyclicHomUniversalModuliClass n := rfl

/-- On the odd chart, the original universal modular object is retained exactly. -/
theorem moduliClass_odd : moduliClass n true =
    OddWeierstrassParameter.cyclicHomUniversalModuliClass n := rfl

/-- Every test retains its original full curve and subgroup under either chart action. -/
theorem moduliClass_relabel (b : Bool) {T : Scheme} (q : T ⟶ locus n b)
    (e : RelabelGroup n) :
    ampleCyclicClassesPullback (q ≫ (relabelAction n b e).hom) n (moduliClass n b) =
      ampleCyclicClassesPullback q n (moduliClass n b) := by
  cases b
  · rw [moduliClass_even, ← UniversalWeierstrass.cyclicHomLocusModuliClass_eq_pullback,
      ← UniversalWeierstrass.cyclicHomLocusModuliClass_eq_pullback]
    exact UniversalWeierstrass.cyclicHomLocusModuliClass_relabel n e.1 e.2.2 q
  · rw [moduliClass_odd, ← OddWeierstrassParameter.cyclicHomLocusModuliClass_eq_pullback,
      ← OddWeierstrassParameter.cyclicHomLocusModuliClass_eq_pullback]
    exact OddWeierstrassParameter.cyclicHomLocusModuliClass_action n q e.2

/-- The existing unrestricted smooth cover remains a cover after arbitrary chart relabeling. -/
theorem exists_relabeled_moduli_fppf_cover {S : Scheme} {E : GeneralizedEllipticCurve S}
    [Smooth E.curve.hom] (H : E.FiniteSubgroup n) (hc : H.IsCyclic) (ha : H.IsAmple)
    (e : RelabelGroup n) :
    ∃ (C : Scheme.Cover.{0} Scheme.fppfPrecoverage S) (b : C.I₀ → Bool)
      (q : ∀ i : C.I₀, C.X i ⟶ locus n (b i)),
      ∀ i, ampleCyclicClassesPullback (q i ≫ (relabelAction n (b i) e).hom) n
        (moduliClass n (b i)) =
          ampleCyclicClassesPullback (C.f i) n (Quotient.mk _ ⟨⟨E, H⟩, hc, ha⟩) := by
  obtain ⟨C, b, q, hq⟩ := exists_moduli_fppf_cover n H hc ha
  exact ⟨C, b, q, fun i ↦ (moduliClass_relabel n (b i) (q i) e).trans (hq i)⟩

end FLT.Mazur.CyclicCharacteristicAtlas
