/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CanonicalSectionNaturality

/-!
# Composition of canonical section base changes

Two successive canonical section maps agree with the composite square,
using the actual pullback-composition isomorphism and tensor associativity.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct
open Scheme.Modules hiding map_smul
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.IncreasingCechCoefficients
open FCurve Chow

variable {P X T S Q V : Scheme.{0}}
  {p : P ⟶ X} {q : P ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
  {r : Q ⟶ P} {v : Q ⟶ V} {k : V ⟶ T}
  (h : IsPullback p q f g) (h' : IsPullback r v q k) (M : X.Modules)

/-- Composition on generating tensors uses the actual sheaf pullback comparison. -/
lemma globalComparison_comp_tmul (c : Γ(V, ⊤)) (b : Γ(T, ⊤))
    (s : baseSections M f.appTop.hom ⊤) :
    let _ : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
    let _ : Algebra Γ(T, ⊤) Γ(V, ⊤) := k.appTop.hom.toAlgebra
    let _ : Algebra Γ(S, ⊤) Γ(V, ⊤) := (k ≫ g).appTop.hom.toAlgebra
    baseGlobalSectionMap v.appTop.hom ((pullbackComp r p).hom.app M)
        (globalComparison h' ((pullback p).obj M)
          (c ⊗ₜ[Γ(T, ⊤)] globalComparison h M (b ⊗ₜ[Γ(S, ⊤)] s))) =
      globalComparison (h'.paste_horiz h) M ((k.appTop b * c) ⊗ₜ[Γ(S, ⊤)] s) := by
  let _ : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
  let _ : Algebra Γ(T, ⊤) Γ(V, ⊤) := k.appTop.hom.toAlgebra
  let _ : Algebra Γ(S, ⊤) Γ(V, ⊤) := (k ≫ g).appTop.hom.toAlgebra
  rw [globalComparison_tmul, globalComparison_tmul, map_smul, globalComparison_tmul]
  change Q.presheaf.map (𝟙 _) (v.appTop c) • ((pullbackComp r p).hom.app M).app ⊤
    (pullGlobal r ((pullback p).obj M)
      (P.presheaf.map (𝟙 _) (q.appTop b) • pullGlobal p M s)) = _
  have hQ (a : Γ(Q, ⊤)) : Q.presheaf.map (𝟙 _) a = a :=
    congrArg (fun z ↦ z a) (Q.presheaf.map_id _)
  have hP (a : Γ(P, ⊤)) : P.presheaf.map (𝟙 _) a = a :=
    congrArg (fun z ↦ z a) (P.presheaf.map_id _)
  rw [hQ, hP]
  change v.appTop c • ((pullbackComp r p).hom.app M).app ⊤
    (pullGlobal r ((pullback p).obj M) (q.appTop b • pullGlobal p M s)) = _
  rw [map_smulₛₗ, Hom.app_smul, pullGlobal_comp_hom]
  have hw := congrArg (fun a : Q ⟶ T ↦ a.appTop b) h'.w
  change r.appTop (q.appTop b) = v.appTop (k.appTop b) at hw
  rw [hw]
  change v.appTop c • (v.appTop (k.appTop b) • pullGlobal (r ≫ p) M s) =
    Q.presheaf.map (𝟙 _) (v.appTop (k.appTop b * c)) • pullGlobal (r ≫ p) M s
  rw [hQ, smul_smul, map_mul, mul_comm (v.appTop c)]

/-- The complete tensor comparison commutes with composition of cartesian squares. -/
lemma globalComparison_comp :
    let _ : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
    let _ : Algebra Γ(T, ⊤) Γ(V, ⊤) := k.appTop.hom.toAlgebra
    let _ : Algebra Γ(S, ⊤) Γ(V, ⊤) := (k ≫ g).appTop.hom.toAlgebra
    let _ : IsScalarTower Γ(S, ⊤) Γ(T, ⊤) Γ(V, ⊤) :=
      IsScalarTower.of_algebraMap_eq' rfl
    (baseGlobalSectionMap v.appTop.hom ((pullbackComp r p).hom.app M)).comp
        ((globalComparison h' ((pullback p).obj M)).comp
          (AlgebraTensorModule.lTensor Γ(V, ⊤) Γ(V, ⊤) (globalComparison h M))) =
      (globalComparison (h'.paste_horiz h) M).comp
        (AlgebraTensorModule.cancelBaseChange Γ(S, ⊤) Γ(T, ⊤) Γ(V, ⊤) Γ(V, ⊤)
          (baseSections M f.appTop.hom ⊤)).toLinearMap := by
  let _ : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
  let _ : Algebra Γ(T, ⊤) Γ(V, ⊤) := k.appTop.hom.toAlgebra
  let _ : Algebra Γ(S, ⊤) Γ(V, ⊤) := (k ≫ g).appTop.hom.toAlgebra
  let _ : IsScalarTower Γ(S, ⊤) Γ(T, ⊤) Γ(V, ⊤) :=
    IsScalarTower.of_algebraMap_eq' rfl
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul c x =>
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [tmul_add, map_add, hx, hy]
    | tmul b s => exact globalComparison_comp_tmul h h' M c b s

end FLT.Mazur.IncreasingCechCoefficients
