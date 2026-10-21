/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticTerminalIntersection
public import FLT.Mazur.PrincipalOpenTensorRange
public import FLT.Mazur.SchemePairBoundaryTransfer

/-!
# Terminal boundary transfer on actual arithmetic pair domains

At every quotient order, change the first input to the terminal divided chart
on the full incidence-open domain of its relative product with any second
input. The actual resolved arithmetic inputs, and hence their contractions,
are unchanged. The transferred first abscissa is nonzero throughout.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages WeierstrassSuccessiveX
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (m j : ℕ) (hj : j + 1 ≤ n)
local notation "Q" => Quotient R π m
local notation "e" => data ⟨j + 1, Nat.lt_succ_of_le hj⟩
local notation "x" => WeierstrassDilatation.x W (π ^ (start + j + 1))
  (Data.b3 e) (Data.b4 e) (Data.b6 e)
local notation "t" => coord W (π ^ (start + j)) π (Data.b3 e) (Data.b4 e) (Data.b6 e) 0
local notation "tt" => tensorCoord W (π ^ (start + j)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e) Q 0
local notation "tu" => WeierstrassDilatation.tensorX W (π ^ (start + j + 1))
  (Data.b3 e) (Data.b4 e) (Data.b6 e) Q
local notation "A" => PrincipalOpenTensor.transitionIso Q x t
  (depthOverlapEquiv W π (start + j) (Data.b3 e) (Data.b4 e) (Data.b6 e))
local notation "a" => PrincipalOpenTensor.inclusion Q t
local notation "b" => (A).hom ≫ PrincipalOpenTensor.inclusion Q x
local notation "old" => finiteArithmeticNewestTensorChart hπ data m j hj
local notation "next" => finiteArithmeticDividedTensorChart hπ data m (j + 1) hj
local notation "s" => finiteGlobalArithmeticStructure hπ data (j + 1) hj m
local notation "f" => old ≫ s
local notation "f'" => next ≫ s
local notation "H" => (terminalArithmeticTensor_isPullback hπ data m j hj).flip
variable {Y : Scheme}
  (g : Y ⟶ Spec (.of (PolygonArithmeticStages.Quotient R π m)))

/-- The whole incidence-open domain in the original older arithmetic relative pair. -/
def arithmeticTerminalPairOpen : (pullback f g).Opens :=
  SchemePairBoundaryTransfer.domain f g a

local notation "O" => arithmeticTerminalPairOpen hπ data m j hj g

/-- The pair domain is exactly the nonvanishing locus of the first incidence coordinate. -/
theorem arithmeticTerminalPairOpen_mem (p : (pullback f g : Scheme)) :
    p ∈ O ↔ tt ∉ (pullback.fst f g p).asIdeal := by
  change pullback.fst f g p ∈ Set.range a ↔ _
  exact PrincipalOpenTensor.mem_inclusion_range Q t _

/-- The original common boundary gives a scheme map to the terminal arithmetic pair. -/
def arithmeticTerminalPairTransfer : (O).toScheme ⟶ pullback f' g :=
  SchemePairBoundaryTransfer.transfer f f' g a b (by
    simpa only [Category.assoc] using congrArg (fun k => k ≫ s) (H).w)

local notation "transfer" => arithmeticTerminalPairTransfer hπ data m j hj g

/-- Both actual first inputs agree in the resolved arithmetic stage. -/
@[reassoc] theorem arithmeticTerminalPairTransfer_first :
    transfer ≫ pullback.fst f' g ≫ next = (O).ι ≫ pullback.fst f g ≫ old :=
  SchemePairBoundaryTransfer.transfer_first_ambient f f' g a b _ old next (H).w

/-- The second input retains its entire original morphism. -/
@[reassoc] theorem arithmeticTerminalPairTransfer_second :
    transfer ≫ pullback.snd f' g = (O).ι ≫ pullback.snd f g :=
  SchemePairBoundaryTransfer.transfer_snd f f' g a b _

/-- The new coordinates stay in the full divided puncture on the whole pair domain. -/
theorem arithmeticTerminalPairTransfer_punctured (p : (O).toScheme) :
    tu ∉ (pullback.fst f' g (transfer p)).asIdeal := by
  have he := congrArg (fun k => k p)
    (SchemePairBoundaryTransfer.transfer_fst f f' g a b (by
      simpa only [Category.assoc] using congrArg (fun k => k ≫ s) (H).w))
  change pullback.fst f' g (transfer p) = b _ at he
  rw [he]
  exact (PrincipalOpenTensor.mem_inclusion_range Q x _).mp ⟨_, rfl⟩

/-- Any subsequent contraction of the actual first input is preserved as a whole morphism. -/
@[reassoc] theorem arithmeticTerminalPairTransfer_contraction {Z : Scheme}
    (c : finiteGlobalArithmeticStage hπ data (j + 1) hj m ⟶ Z) :
    transfer ≫ pullback.fst f' g ≫ next ≫ c =
      (O).ι ≫ pullback.fst f g ≫ old ≫ c := by
  rw [arithmeticTerminalPairTransfer_first_assoc]

end FLT.Mazur.WeierstrassDividedDepth
