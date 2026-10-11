/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineTensorCocycle
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Multiplicative affine descent coactions

A ring coaction with the counit and cocycle equations gives the existing
module equalizer diagram. Its fixed elements form an actual subalgebra; this
constructs the candidate affine coordinate ring without assuming effectivity.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits TensorProduct
namespace FLT.Mazur.AffineAlgebraDescent
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R S B : Type u} [CommRing R] [CommRing S] [CommRing B]
  [Algebra R S] [Algebra R B] [Algebra S B] [IsScalarTower R S B]

/-- Multiplicative descent data: a coaction with its counit and coassociativity laws. -/
structure Data (R S B : Type u) [CommRing R] [CommRing S] [CommRing B]
    [Algebra R S] [Algebra R B] [Algebra S B] [IsScalarTower R S B] where
  /-- The specified algebra coaction. -/
  coaction : B →ₐ[S] S ⊗[R] B
  /-- Restriction to the diagonal recovers every coefficient. -/
  counit (b : B) :
    TensorProduct.lift (Algebra.lsmul R R B (A := S)).toLinearMap (coaction b) = b
  /-- The two transports agree over the triple overlap. -/
  coassoc (b : B) :
    (coaction.toLinearMap.restrictScalars R).lTensor S (coaction b) =
      AffineTensorCocycle.insertMiddle (1 : S) (coaction b)

variable (D : Data R S B)

/-- The descended coordinate ring consists of the fixed coefficients. -/
def invariants : Subalgebra R B :=
  (D.coaction.restrictScalars R).equalizer Algebra.TensorProduct.includeRight

/-- Membership retains the specified coaction, not merely an abstract isomorphic datum. -/
theorem mem_invariants (b : B) : b ∈ invariants D ↔ D.coaction b = 1 ⊗ₜ[R] b := Iff.rfl

/-- The inclusion of fixed coefficients as an original base-linear map. -/
def inclusion : ModuleCat.of R (invariants D) ⟶ ModuleCat.of R B :=
  ModuleCat.ofHom (invariants D).val.toLinearMap

/-- The coaction and the unit define the original fixed-coefficient fork. -/
def invariantFork : Fork (ModuleCat.ofHom (D.coaction.toLinearMap.restrictScalars R))
    (ModuleCat.ofHom (TensorProduct.mk R S B 1)) :=
  Fork.ofι (inclusion D) (by
    apply ModuleCat.hom_ext
    exact LinearMap.ext (fun b ↦ b.property))

/-- The constructed subalgebra is the equalizer of the two original coefficient maps. -/
def invariantForkIsLimit : IsLimit (invariantFork D) := by
  apply Fork.IsLimit.mk'
  intro s
  let l : s.pt →ₗ[R] invariants D :=
    s.ι.hom.codRestrict (invariants D).toSubmodule (fun b ↦
      ConcreteCategory.congr_hom s.condition b)
  refine ⟨ModuleCat.ofHom l, rfl, ?_⟩
  intro m hm
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro b
  exact Subtype.ext (ConcreteCategory.congr_hom hm b)

end FLT.Mazur.AffineAlgebraDescent
