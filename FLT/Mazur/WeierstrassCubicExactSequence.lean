/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCubicLocalKernel
public import FLT.Mazur.WeierstrassCubicMultiplicationMono
public import FLT.Mazur.ModuleSubobjectCoverEquality

/-!
# The short exact sequence of the actual plane cubic

The original cubic equation annihilates the actual quotient on each chart.
Affine local divisibility supplies lifts; injectivity makes these lifts glue.
Thus the constructed O(-3), structure module, and original closed pushforward
form a short exact sequence over every domain, without a smoothness assumption.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open FLT.Mazur.ProjectiveSpace FLT.Mazur.FCurve
open FLT.Mazur.FCurve.ModuleSheafUnitCocycle

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type} [CommRing R] (W : WeierstrassCurve R)

/-- The equation still vanishes after restriction to any subopen of its chart. -/
theorem cubicEquationSection_restrict_quotient_zero (j : Fin 3)
    {V : (space R (Fin 3)).Opens} (h : V ≤ chart R (Fin 3) j) :
    (integralProjectiveMap W).app V (res h (cubicEquationSection W j)) = 0 := by
  have he := ConcreteCategory.congr_hom
    ((integralProjectiveMap W).naturality (homOfLE h).op) (cubicEquationSection W j)
  change (integralProjectiveMap W).app V (res h (cubicEquationSection W j)) = _ at he
  rw [CommRingCat.comp_apply, cubicEquationSection_quotient_zero, map_zero] at he
  exact he

/-- The two genuine morphisms compose to zero over every commutative base ring. -/
theorem cubicStructureMultiply_quotient :
    cubicStructureMultiply W ≫ cubicStructureQuotient W = 0 := by
  apply ModuleSheafMorphismGluing.hom_ext (chart R (Fin 3)) (iSup_chart R (Fin 3))
  intro j
  apply SheafOfModules.hom_ext
  ext V s
  change (integralProjectiveMap W).app V.unop.left
    ((cubicStructureMultiply W).app V.unop.left s) = 0
  rw [cubicStructureMultiply_onChart W j (leOfHom V.unop.hom), map_mul,
    cubicEquationSection_restrict_quotient_zero, mul_zero]

/-- The concrete cubic complex, with the original closed immersion as its quotient. -/
def cubicStructureComplex : ShortComplex (space R (Fin 3)).Modules :=
  ShortComplex.mk (cubicStructureMultiply W) (cubicStructureQuotient W)
    (cubicStructureMultiply_quotient W)

variable [IsDomain R]

/-- Every sheaf map annihilated by the quotient has sectionwise lifts through O(-3). -/
theorem cubicStructureKernel_lifts {M : (space R (Fin 3)).Modules}
    (k : M ⟶ structureModule (space R (Fin 3))) (hk : k ≫ cubicStructureQuotient W = 0)
    (U : (space R (Fin 3)).Opens) (s : Γ(M, U)) :
    ∃ t, (cubicStructureMultiply W).app U t = k.app U s := by
  apply ModuleSubobjectCoverEquality.sections_of_local k (cubicStructureMultiply W) _ U s
  intro V t x hx
  have hxcover : x ∈ iSup (chart R (Fin 3)) := by rw [iSup_chart]; trivial
  obtain ⟨j, hj⟩ := Opens.mem_iSup.mp hxcover
  obtain ⟨_, ⟨A, hA, rfl⟩, hxA, hAV⟩ :=
    (space R (Fin 3)).isBasis_affineOpens.exists_subset_of_mem_open
      (show x ∈ V ⊓ chart R (Fin 3) j from ⟨hx, hj⟩) (V ⊓ chart R (Fin 3) j).isOpen
  refine ⟨A, hAV.trans inf_le_left, hxA, ?_⟩
  apply cubicQuotient_affine_lift W j ⟨A, hA⟩ (hAV.trans inf_le_right)
  exact congrArg (fun f => f.app A
    (ModuleSheafMorphismGluing.res M (hAV.trans inf_le_left) t)) hk

/-- The specified multiplication realizes the categorical kernel of the original quotient. -/
def cubicStructureKernelIsLimit : IsLimit
    (KernelFork.ofι (cubicStructureMultiply W) (cubicStructureMultiply_quotient W)) :=
  KernelFork.IsLimit.ofι' _ _ (fun k hk =>
    ⟨ModuleSubobjectCoverEquality.factor k (cubicStructureMultiply W)
        (cubicStructureKernel_lifts W k hk),
      ModuleSubobjectCoverEquality.factor_comp k (cubicStructureMultiply W)
        (cubicStructureKernel_lifts W k hk)⟩)

/-- Exactness identifies O(-3) with the actual ideal sheaf of the original cubic. -/
theorem cubicStructureComplex_exact : (cubicStructureComplex W).Exact :=
  (cubicStructureComplex W).exact_of_f_is_kernel (cubicStructureKernelIsLimit W)

/-- The actual plane cubic has the short exact sequence O(-3) → O → i_*O_C. -/
theorem cubicStructureComplex_shortExact : (cubicStructureComplex W).ShortExact :=
  ShortComplex.ShortExact.mk' (cubicStructureComplex_exact W)
    (inferInstanceAs (Mono (cubicStructureMultiply W)))
    (inferInstanceAs (Epi (cubicStructureQuotient W)))

end FLT.Mazur.WeierstrassIntegralChart
