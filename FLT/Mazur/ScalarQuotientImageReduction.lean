/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ScalarQuotientImagePresentation
public import FLT.Mazur.QuotientImageReduction
public import FLT.Mazur.FiniteErrorReducedInclusion

/-!
# Image reduction after extending the relative numerator module

Both the ideal and all internal multiples are over the new scalar ring.
Finiteness, residual vanishing, and the second reduction kernel are separate
conditions on the extended preimage, before applying Nakayama.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.ScalarQuotientImagePresentation
variable {R M D : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup D] [Module R D]
  (S : Type*) [CommRing S] [Algebra R S]
  (K : Submodule R M) (g : D →ₗ[R] M ⧸ K) (H : Submodule R M)
  (hH : (LinearMap.range g).comap K.mkQ = H)
set_option quotPrecheck false
local notation "Ks" => K.baseChange S
local notation "Hs" => H.baseChange S
local notation "Q" => LinearMap.range (presentedMap S K g)

include hH in
/-- The lost image kernel is computed inside the extended compatible numerator module. -/
theorem reduction_injective_iff (J : Ideal S) :
    Function.Injective (SubmoduleReduction.inclusion J Q) ↔
      Hs ⊓ (Ks ⊔ J • (⊤ : Submodule S (S ⊗[R] M))) = Ks ⊔ J • Hs := by
  rw [QuotientImageReduction.inclusion_injective_iff_preimage,
    preimage_presentedMap S K g H hH]

include hH in
/-- Residual vanishing is a containment separate from image reduction injectivity. -/
theorem residual_vanishing_iff (J : Ideal S) :
    Q ≤ J • (⊤ : Submodule S ((S ⊗[R] M) ⧸ Ks)) ↔
      Hs ≤ Ks ⊔ J • (⊤ : Submodule S (S ⊗[R] M)) := by
  rw [QuotientImageReduction.residual_vanishing_iff_preimage,
    preimage_presentedMap S K g H hH]

include hH in
/-- Finite generators modulo extended corrections suffice; H itself need not be finite. -/
theorem range_fg_of_relative_generators (E : Submodule S (S ⊗[R] M)) (hE : E.FG)
    (hgen : Ks ⊔ E = Hs) : (Q).FG := by
  have he := congrArg (Submodule.map (Ks).mkQ) hgen
  rw [Submodule.map_sup, Submodule.mkQ_map_self, bot_sup_eq] at he
  rw [range_presentedMap S K g H hH, ← he]
  exact hE.map _

include hH in
/-- The three distinct numerator conditions kill the actual extended map over a local ring. -/
theorem baseChange_eq_zero_of_relative_generators [IsLocalRing S]
    (E : Submodule S (S ⊗[R] M)) (hE : E.FG) (hgen : Ks ⊔ E = Hs)
    (habs : Hs ⊓ (Ks ⊔ IsLocalRing.maximalIdeal S • ⊤) =
      Ks ⊔ IsLocalRing.maximalIdeal S • Hs)
    (hres : Hs ≤ Ks ⊔ IsLocalRing.maximalIdeal S • ⊤) : g.baseChange S = 0 := by
  apply (presentedMap_eq_zero_iff S K g).mp
  apply LinearMap.range_eq_bot.mp
  exact FiniteErrorReduction.eq_bot_of_reduced_inclusion _
    (range_fg_of_relative_generators S K g H hH E hE hgen)
    ((reduction_injective_iff S K g H hH _).mpr habs)
    ((residual_vanishing_iff S K g H hH _).mpr hres)

end FLT.Mazur.ScalarQuotientImagePresentation
