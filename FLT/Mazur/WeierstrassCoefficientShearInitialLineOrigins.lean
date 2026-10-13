/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearInitialFiber
public import FLT.Mazur.WeierstrassCoefficientShearStageIso
public import FLT.Mazur.WeierstrassModificationXIncidenceLineSections

/-!
# The original ordered line-conic attachments in the coefficient gluing

Both marked points agree as actual scheme morphisms, at every finite stage.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Polynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [CommRing S] [Algebra R S] (r : S) (j : ℕ) (hj : j ≤ n)
  (hs : algebraMap R S (π ^ start) = 0)
  (h3 : algebraMap R S (Data.b3 (data ⟨0, Nat.zero_lt_succ n⟩)) = 0)
  (h4 : algebraMap R S (Data.b4 (data ⟨0, Nat.zero_lt_succ n⟩)) = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
local notation "a" => (rootShearCurve (W.map (algebraMap R S)) r).a₁
local notation "c" => algebraMap R S (data ⟨0, Nat.zero_lt_succ n⟩).b6
local notation "L" => coefficientShearInitialLine hπ data S r j hj hs h3 h4 hr
local notation "C₀" => coefficientShearInitialConic hπ data S r j hj hs h3 h4 hr
variable (ha : IsUnit (rootShearCurve (W.map (algebraMap R S)) r).a₁)

/-- The first line marking is the first conic incidence marking in the actual target. -/
@[reassoc] theorem coefficientShearInitialLine_first :
    Spec.map (CommRingCat.ofHom (aeval (0 : S)).toRingHom) ≫ L =
      Spec.map (CommRingCat.ofHom (conicFirstIncidencePoint a c ha).toRingHom) ≫ C₀ := by
  rw [coefficientShearInitialLine, incidenceLineFirstSection_spec_assoc a c ha,
    coefficientShearInitialConic, ← Category.assoc]
  congr 1
  change Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp]
  exact congrArg (fun q => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom q)))
    (fullFirstIncidencePoint_conic a c ha)

/-- The opposite line marking is the original opposite conic incidence marking. -/
@[reassoc] theorem coefficientShearInitialLine_second :
    Spec.map (CommRingCat.ofHom (aeval (-a)).toRingHom) ≫ L =
      Spec.map (CommRingCat.ofHom (conicSecondIncidencePoint a c ha).toRingHom) ≫ C₀ := by
  rw [coefficientShearInitialLine, incidenceLineSecondSection_spec_assoc a c ha,
    coefficientShearInitialConic, ← Category.assoc]
  congr 1
  change Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp]
  exact congrArg (fun q => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom q)))
    (fullSecondIncidencePoint_conic a c ha)

/-- Changing only the stage expression preserves the entire initial conic. -/
@[reassoc] theorem coefficientShearInitialConic_stageIso
    (k : ℕ) (hk : k ≤ n) (e : j = k) :
    C₀ ≫ (coefficientShearStageIso hπ data S r j k hj hk e).hom =
      coefficientShearInitialConic hπ data S r k hk hs h3 h4 hr := by
  subst k
  exact Category.comp_id _

end FLT.Mazur.WeierstrassDividedDepth
