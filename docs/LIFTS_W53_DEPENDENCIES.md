# W53: effective finite-flat quotient and the remaining lifting gates

## D1a-flat: constructed on the W52 arithmetic ring

Let U be `hardlyArithmeticObject` and r its universal framed representation.
At the prime p, form the set of open ideals I of U for which the actual tensor
reduction of r modulo I has `HasFlatProlongationAt`. Define J_flat as their
intersection. This construction uses the existing finite-flat group-scheme
predicate; it does not define flatness by an invented equation predicate.

The proofs establish:

1. Reductions modulo I and J embed, via their canonical coefficient maps, into
   their product from the reduction modulo I ∩ J. The embedding is injective
   coordinatewise. The existing product and schematic-closure theorems give a
   finite-flat model at I ∩ J. No restriction on the residue prime is used.
2. Open ideals are closed. Compactness of U makes those finite-flat open
   reductions cofinal above J_flat. Therefore, for every open I,
   J_flat ≤ I if and only if the actual reduction modulo I is finite flat.
3. The residual HR representation, in its previously constructed frame, gives
   a finite-flat residual point. Its kernel proves J_flat is proper.
4. The quotient U/J_flat has the quotient topology and lies in ProartinianCat.
   Each open reduction has a finite-flat model, using the constructed
   coefficient map from the corresponding open reduction of U.
5. For every proartinian coefficient morphism f, its specialization is flat
   exactly when J_flat ≤ ker f. The forward direction uses schematic closure
   on the kernel quotient and separation by open ideals of the target. The
   reverse direction factors f through the proved flat universal quotient and
   uses the existing coefficient stability theorem.

`hardlyFlatParameterEquiv` is a constructed classification of flat arithmetic
specializations. `hardlyFlatLift` has the same original residual representation,
cyclotomic determinant, unramifiedness away from 2p, specified quotient row at
2, and finite-flat open reductions at p. This is still the specified-frame
condition, not a classification of existential unframed quotient conditions.

The generic intersection and effectivity proofs allow any prime, including 2.
The HR application inherits `Odd p` from `IsHardlyRamified`; it does not extend
that definition to p = 2. The coefficient ring and representation remain in
Type 0, with finite base residue field as in W52.

## D1a-char0: exact obstruction, not an existence proof

`flatClosed_p_nonnilpotent_iff` identifies the missing assertion as

    ∀ m : ℕ, (p : U)^m ∉ J_flat.

`flatClosed_powers_avoid_of_charZero` proves every characteristic-zero ring
specialization requires this assertion. `flatClosed_exists_prime_avoiding_p`
then produces a prime of the actual flat quotient avoiding p, conditional on
that assertion. These results do not prove the assertion. Residual properness
only excludes 1 from J_flat and cannot exclude p or its positive powers.

The current construction allows a characteristic-p base O. The proved
`flatReductionIdeal_contains_power_of_base` shows that any vanishing power
in O already lies in J_flat. Thus characteristic-zero existence cannot hold
under the generic HR quotient's hypotheses: first choose an appropriate
mixed-characteristic base with the specified residual field.

Still required: an arithmetic nonvanishing/dimension argument on this very
quotient, and the topology, finiteness and coefficient-order results needed
to turn an algebraic prime quotient into the intended continuous p-adic lift.
No characteristic-zero solution is claimed, and no isomorphism or evaluation
hypothesis is introduced in place of that argument.

## Lp0: contracts tied to the existing family period objects

These are implementation contracts, not Lean assumptions or fields in a
lifting record. They refine `LIFTS_W46_CRYSTALLINE_CONTRACTS.md` using the
objects already supplied by the family lane. W53's finite-flat effectivity
does not require, construct, or imply a crystalline comparison theorem.

| Contract | Existing inputs | Required theorem or construction |
|---|---|---|
| C0a: crystalline period ring | The family's tilt/theta construction, `ComplexBDeRhamPlus p`, `ComplexBDeRham p`, `PadicGalois p` and their existing actions | Construct B_cris with Frobenius and a Galois-equivariant map into that exact `ComplexBDeRham p`; prove its ring/action/Frobenius laws and fixed scalars. Do not supply a comparison isomorphism as input. |
| C0b: filtered tensor invariants | `ComplexDeRhamIntegerFiltration p`, `complexPadicToDeRhamField p`, `complexCyclotomicFieldPeriod p` | Construct D_cris(V) and D_dR(V) as invariants with their coefficient actions; construct the canonical comparison maps and prove the dimension and filtration statements for the actual representations. |
| C0c: rank-one normalization | `complexDeRham_eigenperiod_existsUnique`, `complexDeRham_scalar_period_smul`, and `complexDeRham_eigenperiod_mem_next_iff` | Recover the trivial character and the covariant cyclotomic Tate twist in B_cris; prove compatibility with the existing B_dR periods. Q_p(1) uses invariant coefficient t^-1 and weight -1. No replacement period field or character evaluation premise. |
| C0d: naturality | Those same period rings, actions and constructed maps | Prove finite coefficient extension, restriction of scalars, dual and tensor compatibility; identify the repository's cyclotomic character, rather than assuming a character comparison. |
| C1: integral levels | Existing finite-flat and p-divisible group objects | Construct the O-action, Tate module and canonical level comparisons. For O-rank two the underlying height is 2[E:Q_p]. Construct pi-power kernels separately when O is ramified. |
| C2: integral recovery | A specified O-lattice T, its rational crystalline property, weights {0,-1} | Construct a p-divisible group over Z_p with O-action recovering that specified lattice. The integral comparison is output. A p > 2 Fontaine–Laffaille theorem does not supply the p = 2 case. |
| C3: actual reductions | C1/C2 and the given coefficient topology | Prove finite-flat models for T/pi^m and openness/cofinality, then use `isFlatAt_iff_of_cofinal_powers` or the general cofinal criterion. |
| C4: relation to this quotient | `hardlyFlatObject` and its proved specialization classification | Compare the characteristic-zero crystalline weight-two condition with this integral finite-flat condition for the intended coefficient orders, in both directions with all lattice hypotheses explicit. |

The existing rank-one de Rham theorems settle their eigenperiod and filtration
calculations. They do not construct B_cris, Frobenius, the general comparison,
or integral Barsotti–Tate classification, including p = 2.

## Later gates retained in priority order

- **S0a2:** compare the finite-DVR uniformizer character to the specified
  absolute tame character, including the needed inertia surjectivity.
- **S0a3:** prove the niveau-two/non-peu cases and symmetric-power composition
  factors. Neither a general Raynaud classification nor a Serre-weight
  evaluation API is assumed to exist.
- **R1:** handle a nontrivial unramified quotient twist, integral base extension
  and descent, and the ramification bound on the intended unramified base.
- Global Selmer/modularity, auxiliary-field, finiteness, coefficient-order and
  residual-conjugacy obligations remain. `IsHardlyRamified.lifts` is unchanged.

The untracked `LIFTS_W53_RESULT.md` records validation and exact commits.
`Scratch/LiftsW53/validate.py` runs serial module builds, serial module lint and
an axiom audit of every new named definition and theorem. No whole-library
lint is part of that check.
