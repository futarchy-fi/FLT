/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LineSectionCohomologySurjection
public import FLT.Mazur.AmpleCoherentVanishing
public import FLT.Mazur.SectionGeneratorSpan

/-!
# Higher cohomology vanishing for lines on proper integral curves

A nonzero section has finite-support transition cokernels. Thus line-twist
cohomology is injective above degree one, and Serre vanishing of a large
ample twist forces the original higher cohomology to vanish.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open Scheme.Modules
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve
open ModuleSheafTensor ModuleLineBundleTensorPullback CoherentDevissage
open LineSectionTwistSystem
variable {k : Type} [Field k] {X : Scheme} [IsIntegral X]
  (f : X ⟶ Spec (.of k)) [IsProper f]

/-- Finite-support transition cokernels give injectivity above degree one. -/
theorem lineStep_higher_cohomology_injective (hd : topologicalKrullDim X ≤ 1)
    {M L : X.Modules} (hM : LocallyFreeRankOne M) (hL : LocallyFreeRankOne L)
    (s : Γ(L, ⊤)) (hs : s ≠ 0) (n q : ℕ) :
    Function.Injective (moduleScalarHMap f (step M s n) (q + 2)) := by
  let _ := Chow.source_isNoetherian f
  let _ := hM.isFinitePresentation
  let _ := (hM.tensor (hL.tensorPower n)).isFinitePresentation
  let _ := (hM.tensor (hL.tensorPower (n + 1))).isFinitePresentation
  let a := step M s n
  let _ := lineStep_mono hM hL s hs n
  let _ := coherent_cokernel a
  have hS := coherent_cokernelSequence a
  let _ : Subsingleton (ModuleScalarH f (ShortComplex.cokernelSequence a).X₃ (q + 1)) :=
    finiteSupport_cohomology_subsingleton f (cokernel a)
      (step_cokernel_finiteSupport hd M hL s hs n) (q + 1) (Nat.succ_pos q)
  have he := moduleScalarH_exact₁ (ShortComplex.cokernelSequence a)
    (moduleToSheaf_shortExact hS.shortExact) f (q + 1)
  apply (moduleScalarHMap f a (q + 2)).ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  obtain ⟨y, hy⟩ := (he x).mp hx
  rw [Subsingleton.elim y 0, map_zero] at hy
  exact hy.symm

/-- Injective successor maps give injectivity of every map in a module sequence. -/
private theorem sequence_map_injective {R : Type} [Ring R] (F : ℕ ⥤ ModuleCat.{1} R)
    (hF : ∀ n, Function.Injective (F.map (homOfLE (Nat.le_add_right n 1))))
    {n m : ℕ} (h : n ≤ m) : Function.Injective (F.map (homOfLE h)) := by
  induction m, h using Nat.le_induction with
  | base => simpa using (Function.injective_id : Function.Injective (id : F.obj n → F.obj n))
  | succ m h ih =>
    have he : homOfLE (show n ≤ m + 1 from h.trans (Nat.le_add_right m 1)) =
        homOfLE h ≫ homOfLE (Nat.le_add_right m 1) := rfl
    rw [he, F.map_comp]
    exact (hF m).comp ih

include f in
/-- Any line on a proper integral curve with an ample line has no cohomology above H¹. -/
theorem curve_line_higher_vanishing (hd : topologicalKrullDim X ≤ 1)
    {B : X.Modules} (hB : AmpleLineBundle B) {M : X.Modules}
    (hM : LocallyFreeRankOne M) (q : ℕ) : Subsingleton (ModuleH M (q + 2)) := by
  let _ := hM.isFinitePresentation
  obtain ⟨d, hdpos, s, hs, _⟩ := hB.2.2 (genericPoint X)
  have hs0 : s ≠ 0 := by
    intro hz
    rw [hz, sectionGeneratorOpen_zero] at hs
    exact hs
  obtain ⟨N, hN⟩ := hB.coherent_vanishing f M
  let F := cohomology f M s (q + 2)
  have hinj : Function.Injective (F.map (homOfLE (Nat.zero_le N))) := by
    apply sequence_map_injective
    intro n
    dsimp only [F]
    rw [cohomology_map_succ]
    exact lineStep_higher_cohomology_injective f hd hM (hB.2.1.tensorPower d) s hs0 n q
  have hbound : N ≤ d * N := by nlinarith
  let e := ModuleSheafTensor.congr (Iso.refl M) (tensorPowerMulIso B d N)
  let _ : Subsingleton (F.obj N) :=
    @moduleH_subsingleton_of_iso X _ _ e (q + 2) (hN (d * N) hbound (q + 1))
  have hz : Subsingleton (F.obj 0) := hinj.subsingleton
  exact @moduleH_subsingleton_of_iso X _ _ (rightUnitor M).symm (q + 2) hz

end FLT.Mazur.FCurve
