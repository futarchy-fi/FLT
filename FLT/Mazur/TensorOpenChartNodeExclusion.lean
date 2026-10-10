/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PrincipalOpenTensorPullback
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Tensor nodes outside a principal boundary miss the entire exterior

The full original exterior intersection and the tensor restriction square
transport a local node exclusion to every chart contained in that exterior.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
open scoped TensorProduct
namespace FLT.Mazur.TensorOpenChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S A : Type u} [CommRing R] [CommRing S] [CommRing A]
  [Algebra R S] [Algebra R A] {X E N : Scheme.{u}}
  (f : X ⟶ Spec (.of R)) (i : Spec (.of A) ⟶ X) (e : E ⟶ X)
  (hi : i ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R A)))
  (x : A) (l : Spec (.of (Localization.Away x)) ⟶ E)
  (H : IsPullback l (Spec.map (CommRingCat.ofHom
    (algebraMap A (Localization.Away x)))) e i)
  (o : N ⟶ Spec (.of (S ⊗[R] A)))
  (ho : Disjoint (Set.range (PrincipalOpenTensor.inclusion S x)) (Set.range o))

include H ho in
/-- A tensor node off the original boundary misses the whole pulled-back exterior. -/
theorem node_exterior_disjoint :
    Disjoint (Set.range (o ≫ chart f i hi))
      ((pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R S))) f) ⁻¹'
        Set.range e) := by
  apply Set.disjoint_left.mpr
  rintro _ ⟨a, rfl⟩ ⟨b, hb⟩
  have hp := congrArg (fun k => k (o a)) (chart_snd (S := S) f i hi)
  have he : e b = i (projection (o a)) := hb.trans hp
  obtain ⟨v, _, hv⟩ := Scheme.exists_preimage_of_isPullback H b (projection (o a)) he
  obtain ⟨w, hw, _⟩ := Scheme.exists_preimage_of_isPullback
    (PrincipalOpenTensor.inclusion_isPullback S x) (o a) v hv.symm
  exact Set.disjoint_left.mp ho ⟨w, hw⟩ ⟨a, rfl⟩

end FLT.Mazur.TensorOpenChart
