/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.GroupScheme.EtaleModelIdentification

/-!
# Constant integral models with one-dimensional trivial points

A one-dimensional trivial mod-three point module has an explicit equivariant
additive comparison with `constantThree`. If its chosen integral model is étale,
the comparison extends to an integral bialgebra equivalence. Without integral
étaleness, the reverse point comparison still extends from the constant model,
and the resulting coordinate map is injective. This separates the generic
representation classification from the remaining integral-model assertion.
-/

@[expose] public noncomputable section

namespace ThreeAdicPlan

local notation "Γ" => AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ

/-- A one-dimensional mod-three point module has the additive group of the
canonical constant-three model. -/
def constantThreePointEquiv (H : FiniteFlatObject ZInvTwo) [Module (ZMod 3) H.points]
    (hdim : Module.finrank (ZMod 3) H.points = 1) : H.points ≃+ constantThree.points :=
  (LinearEquiv.ofFinrankEq (R := ZMod 3) H.points (ZMod 3)
    (hdim.trans (Module.finrank_self (ZMod 3)).symm)).toAddEquiv

/-- Triviality of the given action makes the point comparison equivariant. -/
theorem constantThreePointEquiv_smul (H : FiniteFlatObject ZInvTwo)
    [Module (ZMod 3) H.points] (hdim : Module.finrank (ZMod 3) H.points = 1)
    (htriv : ∀ (σ : Γ) (x : H.points), σ • x = x) (σ : Γ) (x : H.points) :
    constantThreePointEquiv H hdim (σ • x) = σ • constantThreePointEquiv H hdim x := by
  rw [htriv, constantThree_smul]

/-- A one-dimensional integral étale model with trivial Galois action is the
canonical constant-three model, with the specified point comparison. -/
theorem exists_iso_constantThree_of_etale (H : FiniteFlatObject ZInvTwo)
    [Module (ZMod 3) H.points] [Algebra.Etale ZInvTwo H.model.CoordinateRing]
    (hdim : Module.finrank (ZMod 3) H.points = 1)
    (htriv : ∀ (σ : Γ) (x : H.points), σ • x = x) :
    ∃ i : H.Iso constantThree,
      ∀ x, FiniteFlatObject.pointMap i.toBialgHom x = constantThreePointEquiv H hdim x := by
  let : Algebra.Etale ZInvTwo constantThree.model.CoordinateRing := constantThree_etale
  exact H.exists_iso_of_etale constantThree (constantThreePointEquiv H hdim)
    (constantThreePointEquiv_smul H hdim htriv)

/-- Even before integral étaleness is known, the inverse point comparison extends
from the constant model. Its integral coordinate map is injective. -/
theorem exists_constantThree_hom_of_trivial (H : FiniteFlatObject ZInvTwo)
    [Module (ZMod 3) H.points] (hdim : Module.finrank (ZMod 3) H.points = 1)
    (htriv : ∀ (σ : Γ) (x : H.points), σ • x = x) :
    ∃ f : constantThree.Hom H, Function.Injective f ∧
      ∀ x, FiniteFlatObject.pointMap f x = (constantThreePointEquiv H hdim).symm x := by
  let e := constantThreePointEquiv H hdim
  let g : GenericGaloisHom constantThree.toFF H.toFF :=
    { toAddMonoidHom := e.symm.toAddMonoidHom
      map_smul' := fun σ x ↦ by
        change e.symm (σ • (show constantThree.points from x)) = σ • e.symm x
        rw [constantThree_smul, htriv] }
  let : Algebra.Etale ZInvTwo constantThree.model.CoordinateRing := constantThree_etale
  let : Algebra.Etale ZInvTwo constantThree.toFF.CoordinateRing := constantThree_etale
  obtain ⟨f, hf, _⟩ := extend_generic_morphism_of_etale constantThree.toFF H.toFF g
  refine ⟨f, ?_, fun x ↦ DFunLike.congr_fun hf x⟩
  apply ModelHom.injective_of_baseChange_injective (X := constantThree.toFF) (Y := H.toFF)
  rw [← ModelHom.toBialgHom_genericHom, hf]
  exact g.toBialgHom_injective e.symm.surjective

/-- In the trivial one-dimensional case, identification of the actual integral
model is equivalent to its integral étaleness. -/
theorem nonempty_iso_constantThree_iff_etale (H : FiniteFlatObject ZInvTwo)
    [Module (ZMod 3) H.points] (hdim : Module.finrank (ZMod 3) H.points = 1)
    (htriv : ∀ (σ : Γ) (x : H.points), σ • x = x) :
    Nonempty (H.Iso constantThree) ↔ Algebra.Etale ZInvTwo H.model.CoordinateRing := by
  constructor
  · rintro ⟨i⟩
    let : Algebra.Etale ZInvTwo constantThree.model.CoordinateRing := constantThree_etale
    exact Algebra.Etale.of_equiv i.toAlgEquiv
  · intro h
    let := h
    obtain ⟨i, _⟩ := exists_iso_constantThree_of_etale H hdim htriv
    exact ⟨i⟩

end ThreeAdicPlan
