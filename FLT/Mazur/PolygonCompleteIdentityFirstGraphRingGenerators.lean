/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFirstGraphScheme

/-!
# Ring generators of the original finite graph

The full source node ring and the two original target coordinates generate
the finite graph as a ring. This formulation also applies to global-section
maps which have not yet been equipped with a scalar algebra structure.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing LaurentFirstStageParameter
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] completeIdentityFirstActionUnit completeIdentityFirstActionField
  completeIdentityFirstActionNodeDefect completeIdentityFirstErrorAlgebra
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "S" => Ring K[T;T⁻¹] 1
local notation "e" => parameter K[T;T⁻¹] 1
local notation "B" => ChartRing (e)
local notation "E" => completeIdentityFirstErrorAlgebra K n h i
local notation "s" => completeIdentityFirstGraphSource K n h i
local notation "d" => completeIdentityFirstGraphTarget K n h i
local notation "σ" => reciprocalScale (e) (parameterUnit K)

/-- Cache the graph ring before forming its subrings and ring homomorphisms. -/
local instance completeIdentityFirstGraphGeneratorsCommRing : CommRing (E) := inferInstance

/-- Every subring containing the source and the two target coordinates is the full graph. -/
theorem completeIdentityFirstGraph_subring_eq_top (C : Subring (E))
    (hs : ∀ z : B, (s) z ∈ C)
    (hx : (d) (leftCoordinate (e)) ∈ C)
    (hy : (d) (rightCoordinate (e)) ∈ C) : C = ⊤ := by
  apply top_unique
  intro z _
  obtain ⟨a, b, c, hz⟩ := completeIdentityFirstErrorAlgebra_normalForm K n h i z.val z.property
  obtain ⟨a', ha⟩ := (firstNodeBranchEquiv K[T;T⁻¹]).surjective a
  obtain ⟨b', hb⟩ := (firstNodeBranchEquiv K[T;T⁻¹]).surjective b
  obtain ⟨c', hc⟩ := (firstNodeBranchEquiv K[T;T⁻¹]).surjective c
  have hv (w : B) : ((firstNodeBranchEquiv K[T;T⁻¹]) w).val =
      firstNodeBranchPair K[T;T⁻¹] w := rfl
  have he : z = (s) a' + (s) b' * ((d) (leftCoordinate (e)) -
      (s) ((σ) (leftCoordinate (e)))) + (s) c' * ((d) (rightCoordinate (e)) -
      (s) ((σ) (rightCoordinate (e)))) := by
    apply Subtype.ext
    simp only [Subalgebra.coe_add, Subalgebra.coe_mul, Subalgebra.coe_sub,
      completeIdentityFirstGraphSource_apply, completeIdentityFirstGraphTarget_apply]
    simpa only [completeIdentityFirstGraphSource_apply,
      completeIdentityFirstGraphTarget_apply, completeIdentityFirstActionNodeDefect_apply,
      ← ha, ← hb, ← hc, hv] using hz
  rw [he]
  exact C.add_mem (C.add_mem (hs _) (C.mul_mem (hs _) (C.sub_mem hx (hs _))))
    (C.mul_mem (hs _) (C.sub_mem hy (hs _)))

/-- Lifting the source and both target coordinates suffices for surjectivity onto the graph. -/
theorem completeIdentityFirstGraph_surjective_of_generators {T : Type*} [CommRing T]
    (f : T →+* (E)) (hs : ∀ z : B, (s) z ∈ f.range)
    (hx : (d) (leftCoordinate (e)) ∈ f.range)
    (hy : (d) (rightCoordinate (e)) ∈ f.range) : Function.Surjective f := by
  have he := completeIdentityFirstGraph_subring_eq_top K n h i f.range hs hx hy
  intro z
  have hz : z ∈ f.range := he.symm ▸ (show z ∈ (⊤ : Subring (E)) from trivial)
  exact hz

end FLT.Mazur.PolygonInfinitesimalStages
