/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeConnectingImagePreimage
public import FLT.Mazur.QuotientImageReduction

/-!
# The image reduction kernel in the original mixed module

The image-to-relative reduction is injective precisely when compatible
errors in K + JN already lie in K + JH, where H consists of discrepancies
of actual compatible families. This is distinct from the N-to-ambient test.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.QuotientImageReduction
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  (J : Ideal R) (N K H : Submodule R M) (hKN : K ≤ N) (hHN : H ≤ N)
  (Q : Submodule R (N ⧸ K.comap N.subtype))
  (hQ : Q.comap (K.comap N.subtype).mkQ = H.comap N.subtype)

include hKN hHN hQ in
/-- The image reduction test transports through a proved preimage identity without unfolding Q. -/
theorem inclusion_injective_iff_relative_preimage :
    Function.Injective (SubmoduleReduction.inclusion J Q) ↔
      H ⊓ (K ⊔ J • N) = K ⊔ J • H := by
  rw [inclusion_injective_iff_preimage, hQ]
  have hmapH : (H.comap N.subtype).map N.subtype = H := by
    rw [Submodule.map_comap_subtype, inf_eq_right.mpr hHN]
  have hmapK : (K.comap N.subtype).map N.subtype = K := by
    rw [Submodule.map_comap_subtype, inf_eq_right.mpr hKN]
  have hmapTop : (⊤ : Submodule R N).map N.subtype = N := by
    rw [Submodule.map_top, Submodule.range_subtype]
  constructor
  · intro h
    have he := congrArg (Submodule.map N.subtype) h
    simpa only [Submodule.map_inf N.subtype N.subtype_injective, Submodule.map_sup,
      Submodule.map_smul'', hmapH, hmapK, hmapTop] using he
  · intro h
    apply Submodule.map_injective_of_injective N.subtype_injective
    simpa only [Submodule.map_inf N.subtype N.subtype_injective, Submodule.map_sup,
      Submodule.map_smul'', hmapH, hmapK, hmapTop] using h

end FLT.Mazur.QuotientImageReduction

namespace FLT.Mazur.RelativeBoundaryConnectingMap
variable {R A B C D : Type*} [CommRing R]
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  [AddCommGroup C] [Module R C] [AddCommGroup D] [Module R D]
  (b : A →ₗ[R] B) (δ : A →ₗ[R] C) (N : Submodule R C)
  (β : D →ₗ[R] B) (u : D → A)
  (hb : ∀ t, b (u t) = β t) (hN : ∀ t, δ (u t) ∈ N)
  (hKN : (LinearMap.ker b).map δ ≤ N) (J : Ideal R)
set_option quotPrecheck false
local notation "K" => (LinearMap.ker b).map δ
local notation "H" => compatibleDiscrepancies b δ β
local notation "Q" => LinearMap.range (connecting b δ N β u hb hN)

include hb hN hKN in
/-- Original compatible errors are recovered from their subtype representatives without loss. -/
theorem map_compatibleDiscrepancies_comap : ((H).comap N.subtype).map N.subtype = H := by
  rw [Submodule.map_comap_subtype,
    inf_eq_right.mpr (compatibleDiscrepancies_le b δ N β u hb hN hKN)]

include hKN in
/-- The second reduction kernel has its own internal compatible-error intersection criterion. -/
theorem connecting_image_reduction_injective_iff :
    Function.Injective (SubmoduleReduction.inclusion J Q) ↔
      H ⊓ (K ⊔ J • N) = K ⊔ J • H := by
  exact QuotientImageReduction.inclusion_injective_iff_relative_preimage J N K H hKN
    (compatibleDiscrepancies_le b δ N β u hb hN hKN) Q
    (connecting_range_comap b δ N β u hb hN)

end FLT.Mazur.RelativeBoundaryConnectingMap
