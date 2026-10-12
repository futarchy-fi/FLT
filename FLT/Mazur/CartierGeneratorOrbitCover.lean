/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveCartierGenerator
public import FLT.Mazur.SectionSumFinite

/-!
# A Cartier generator covers the actual subgroup by its orbit

The scheme-theoretic orbit identity implies coverage of every subgroup point.
This applies to non-etale cyclic levels too: the cover is only asserted to be
surjective, and no distinctness or flatness of the orbit map is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory MonObj
open scoped CategoryTheory.Obj
namespace FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} {E : GeneralizedEllipticCurve S} {n : ℕ}
  (H : E.FiniteSubgroup n) {P : 𝟙_ (Over S) ⟶ H.carrier}

/-- Every actual subgroup point is a power of the generator over its own base point. -/
theorem IsCartierGenerator.exists_orbit_point (hP : H.IsCartierGenerator P)
    (x : H.carrier.left) :
    ∃ i : Fin n, (P ^ i.val).left (H.carrier.hom x) = x := by
  have : IsProper E.curve.hom := E.family.family.1
  have hx : H.curveMap.left x ∈ H.ideal.support :=
    H.curveMap.left.range_subset_ker_support ⟨x, rfl⟩
  rw [hP.2.2] at hx
  obtain ⟨i, _, hi⟩ := (FCurve.mem_support_prod Finset.univ
    (fun i : Fin n ↦ ((P ^ i.val) ≫ H.curveMap).left.ker) _).mp hx
  rw [← SetLike.mem_coe, FCurve.support_section_ker E.curve.hom
    ((P ^ i.val) ≫ H.curveMap).left (Over.w _)] at hi
  obtain ⟨s, hs⟩ := hi
  have hp : (P ^ i.val).left s = x := H.curveMap.left.isClosedEmbedding.injective hs
  have hb : s = H.carrier.hom x := by
    have hw := congrArg (fun f : S ⟶ S ↦ f s) (Over.w (P ^ i.val))
    change H.carrier.hom ((P ^ i.val).left s) = s at hw
    rw [hp] at hw
    exact hw.symm
  exact ⟨i, hb ▸ hp⟩

/-- The actual orbit morphism from the finite coproduct of the original base. -/
def generatorOrbitMap (P : 𝟙_ (Over S) ⟶ H.carrier) :
    (∐ fun _ : Fin n ↦ S) ⟶ H.carrier.left :=
  Sigma.desc fun i ↦ (P ^ i.val).left

/-- The orbit map retains every original power section. -/
@[reassoc] theorem generatorOrbitMap_component (P : 𝟙_ (Over S) ⟶ H.carrier)
    (i : Fin n) :
    Sigma.ι (fun _ : Fin n ↦ S) i ≫ H.generatorOrbitMap P = (P ^ i.val).left :=
  Sigma.ι_comp_desc _ _

/-- A Cartier generator gives a surjective orbit morphism, even for non-etale subgroups. -/
theorem IsCartierGenerator.orbit_surjective (hP : H.IsCartierGenerator P) :
    Surjective (H.generatorOrbitMap P) := by
  constructor
  intro x
  obtain ⟨i, hi⟩ := hP.exists_orbit_point H x
  refine ⟨(Sigma.ι (fun _ : Fin n ↦ S) i) (H.carrier.hom x), ?_⟩
  have he := congrArg (fun f : S ⟶ H.carrier.left ↦ f (H.carrier.hom x))
    (H.generatorOrbitMap_component P i)
  exact he.trans hi

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
