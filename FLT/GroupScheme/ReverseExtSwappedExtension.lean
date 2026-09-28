/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.GroupScheme.CyclotomicModelIdentification
public import FLT.GroupScheme.FiniteFlatExtensionQuotientIso
public import FLT.GroupScheme.ReverseExtVanishing
public import FLT.GroupScheme.StableSubgroupExtension

/-!
# Integral swaps of reverse extensions

The actual splitting gives the reversed exact sequence on geometric points.
Flat closure and contraction recover an integral extension of the same middle
model. Identification of its order-three ends, followed by integral transport,
supplies the faithfully flat quotient and the full torsor comparison.
-/

@[expose] public noncomputable section

namespace ThreeAdicPlan

/-- Three-element mod-three point modules have dimension one. -/
theorem FiniteFlatObject.finrankOneOfCardThree (H : FiniteFlatObject ZInvTwo)
    [Module (ZMod 3) H.points] (hcard : Nat.card H.points = 3) :
    Module.finrank (ZMod 3) H.points = 1 := by
  let moduleThree : Module (ZMod 3) (ZMod 3) := inferInstance
  let e : H.points ≃+ ZMod 3 := addEquivOfPrimeCardEq hcard (by simp)
  let l : H.points ≃ₗ[ZMod 3] ZMod 3 :=
    { e with
      map_smul' := by
        intro c x
        change e (c • x) = c • e x
        rw [← ZMod.natCast_zmod_val c, Nat.cast_smul_eq_nsmul,
          Nat.cast_smul_eq_nsmul, map_nsmul] }
  exact l.finrank_eq.trans (Module.finrank_self (ZMod 3))

/-- A reverse extension admits a full integral extension in the opposite order,
with the original middle model and all faithfully flat torsor fields. -/
theorem FiniteFlatExtension.existsSwappedExtension
    {H : FiniteFlatObject ZInvTwo} (E : FiniteFlatExtension constantThree H muThree) :
    Nonempty (FiniteFlatExtension muThree H constantThree) := by
  let s := E.constantThreeMuThreeModelSplitting
  let i : GenericGaloisHom muThree.toFF H.toFF := genericHom s.sectionMap
  let q : GenericGaloisHom H.toFF constantThree.toFF := genericHom s.retraction
  have hi : Function.Injective i := s.swappedPointsExact.1
  have hq : Function.Surjective q := s.swappedPointsExact.2.1
  have hexact : ∀ h, q h = 0 ↔ ∃ a, i a = h := s.swappedPointsExact.2.2
  let A := (i.closure hi).toFiniteFlatObject
  let Q := (q.flatQuotient hq).toFiniteFlatObject
  let F : FiniteFlatExtension A H Q := H.extensionOfGenericExact i q hi hq hexact
  have hAkill : ∀ a : A.points, (3 : ℕ) • a = 0 := muThree_nsmul
  let moduleA : Module (ZMod 3) A.points := AddCommGroup.zmodModule hAkill
  have hAdim : Module.finrank (ZMod 3) A.points = 1 :=
    A.finrankOneOfCardThree muThree_card_points
  have hAcycl : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (a : A.points),
      σ • a = (modThreeCyclotomic σ : ZMod 3) • a := by
    intro σ a
    rw [← ZMod.natCast_zmod_val (modThreeCyclotomic σ : ZMod 3),
      Nat.cast_smul_eq_nsmul]
    exact muThree_modThreeCyclotomic_smul σ a
  obtain ⟨eA⟩ := exists_iso_muThree A hAdim hAcycl
  have hQkill : ∀ a : Q.points, (3 : ℕ) • a = 0 := constantThree_nsmul
  let moduleQ : Module (ZMod 3) Q.points := AddCommGroup.zmodModule hQkill
  have hQdim : Module.finrank (ZMod 3) Q.points = 1 :=
    Q.finrankOneOfCardThree constantThree_card_points
  obtain ⟨eQ, _⟩ := exists_iso_constantThree Q hQdim constantThree_smul
  exact ⟨(F.transportKernel eA).transportQuotient eQ⟩

end ThreeAdicPlan
