/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CurveFiberHypotheses
public import FLT.Mazur.ProperCurveGenus

/-!
# Necessary genus-one nodal geometric fiber conditions

Properness descends to geometric fibers along their pullback squares. Nonemptiness
and pure dimension one supply the dimension hypothesis for genus; constant global
sections remain explicit. These are necessary conditions, not DR stability: the
trivial-dualizing-sheaf or Néron-polygon classification obligation remains separate.

The cohomology finiteness theorem currently applies to schemes and fields in `Type`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace FLT.Mazur.FCurve.CurveFiberHypotheses

/-- Nonempty schemes whose irreducible components have dimension one have dimension one. -/
theorem PureDimensionOne.topologicalKrullDim_eq_one {X : Scheme} [Nonempty X]
    (h : PureDimensionOne X) :
    topologicalKrullDim X = 1 := by
  apply le_antisymm
  · change Order.krullDim (IrreducibleCloseds X) ≤ 1
    rw [Order.krullDim]
    refine iSup_le fun p ↦ ?_
    obtain ⟨Z, hZ, hpZ⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
      (p.last : Set X) p.last.isIrreducible
    have hp (i : Fin (p.length + 1)) : (p i : Set X) ⊆ Z :=
      fun x hx ↦ hpZ (p.monotone (Fin.le_last i) hx)
    let q : Fin (p.length + 1) → IrreducibleCloseds Z := fun i ↦
      { carrier := Subtype.val ⁻¹' (p i : Set X)
        isClosed' := (p i).isClosed.preimage continuous_subtype_val
        isIrreducible' := by
          let := Subtype.irreducibleSpace (p i).isIrreducible
          have he : (fun x : (p i : Set X) ↦ (⟨x.1, hp i x.2⟩ : Z)) '' Set.univ =
              Subtype.val ⁻¹' (p i : Set X) := by
            ext x
            constructor
            · rintro ⟨y, _, rfl⟩
              exact y.2
            · intro hx
              exact ⟨⟨x.1, hx⟩, Set.mem_univ _, Subtype.ext rfl⟩
          rw [← he]
          exact (IrreducibleSpace.isIrreducible_univ _).image _ (by fun_prop) }
    have hq : StrictMono q := by
      intro i j hij
      refine lt_of_le_not_ge (fun x hx ↦ (p.strictMono hij).le hx) ?_
      intro hji
      exact (not_le_of_gt (p.strictMono hij))
        (fun x hx ↦ hji (show (⟨x, hp j hx⟩ : Z) ∈ q j from hx))
    have hd := Order.LTSeries.length_le_krullDim (LTSeries.mk p.length q hq)
    exact hd.trans (le_of_eq (h Z hZ))
  · obtain ⟨x⟩ := ‹Nonempty X›
    rw [← h (irreducibleComponent x) (irreducibleComponent_mem_irreducibleComponents x)]
    exact topologicalKrullDim_subspace_le X _

/-- The dimension hypothesis for genus follows from the nonempty pure nodal core. -/
theorem NodalFiberCore.topologicalKrullDim_eq_one {K : Type} [Field K] {X : Scheme}
    {f : X ⟶ Spec (.of K)} (h : NodalFiberCore f) : topologicalKrullDim X = 1 := by
  let := h.nonempty
  exact h.pureDimension.topologicalKrullDim_eq_one

variable {K : Type} [Field K] {X S : Scheme}

/-- The necessary nodal fiber core with constant sections and actual genus one. -/
structure NodalGenusOneFiberCore (f : X ⟶ Spec (.of K)) [IsProper f] : Prop
    extends NodalFiberCore f where
  constantSections : HasConstantGlobalSections f
  genus_one : curveGenus f toNodalFiberCore.topologicalKrullDim_eq_one constantSections = 1

/-- Necessary genus-one conditions on all geometric-point pullback squares of a proper map.
The fiber's properness is derived from the square, not supplied as another hypothesis. -/
structure NodalGenusOneGeometricFibers (f : X ⟶ S) [IsProper f] : Prop where
  fiber : ∀ (L : Type) [Field L] [IsAlgClosed L]
    (s : Spec (.of L) ⟶ S) {Y : Scheme}
    (fst : Y ⟶ X) (snd : Y ⟶ Spec (.of L)) (hs : IsPullback fst snd f s),
    let : IsProper snd := MorphismProperty.of_isPullback hs (inferInstance : IsProper f)
    NodalGenusOneFiberCore snd

/-- The canonical geometric pullback satisfies the necessary genus-one nodal contract. -/
theorem NodalGenusOneGeometricFibers.pullback {f : X ⟶ S} [IsProper f]
    (h : NodalGenusOneGeometricFibers f) [IsAlgClosed K] (s : Spec (.of K) ⟶ S) :
    NodalGenusOneFiberCore (pullback.snd f s) :=
  h.fiber K s _ _ (.of_hasPullback f s)

/-- Forgetting genus retains every condition of the existing nodal geometric fiber core. -/
theorem NodalGenusOneGeometricFibers.toNodalGeometricFibers {f : X ⟶ S} [IsProper f]
    (h : NodalGenusOneGeometricFibers f) : NodalGeometricFibers f := by
  refine ⟨fun L _ _ s Y fst snd hs ↦ ?_⟩
  let : IsProper snd := MorphismProperty.of_isPullback hs (inferInstance : IsProper f)
  exact (h.fiber L s fst snd hs).toNodalFiberCore

end FLT.Mazur.FCurve.CurveFiberHypotheses
