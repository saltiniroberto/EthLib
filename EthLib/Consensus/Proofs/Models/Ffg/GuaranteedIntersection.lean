module

public import EthLib.Consensus.Proofs.Models.Stake
public import Mathlib.Order.Lattice.Nat

/-!
# Casper FFG: the guaranteed intersection of two quorums up to slack

A slack link counts the stake of its voters against the validator set `L` of its target.

The voters hold two thirds of the stake of `L`, up to twice the slack.

The slack is the stake of the validators of `L` outside a second set `L'`.

Call such a set of voters a quorum of `L` up to the slack of `L'`.

Two links whose double voters are slashable make the voters of both links slashable.

So the slashable stake is at least the stake that the two quorums share.

The guaranteed intersection is the least stake that two such quorums share.

It depends only on the two pairs of sets and on the weights of each quorum.

So a safety bound in its terms needs no fact about the voters of the two links.

The proof of Gasper Theorem 8.3 bounds this shared stake with arithmetic on the two sets.

The paper is [arXiv 2003.03052v3](https://arxiv.org/abs/2003.03052v3).

The guaranteed intersection is the exact least value, so it is at least each such bound.
-/

@[expose] public section

namespace EthLib.Consensus.Models.Ffg

variable {ν : Type*}

open scoped Classical in
/-- The least stake under `wl` that a quorum of `L` and a quorum of `R` share.

A quorum of `L` is a set `A ⊆ L` with the bound of a slack link under the weights `wl`.

```text
    2 * wl(L) ≤ 3 * wl(A) + 2 * wl(L \ L')
```

A quorum of `R` is a set `B ⊆ R` with the same bound for `R` and `R'` under the weights `wr`.

The shared stake of `A` and `B` is counted under `wl`.

The set `L` is a quorum of `L`, and `R` of `R`, so the minimum is over a nonempty set. -/
noncomputable def guaranteedIntersection (L L' R R' : Finset ν) (wl wr : ν → ℕ) : ℕ :=
  sInf {shared | ∃ A ⊆ L, ∃ B ⊆ R, 2 * stake wl L ≤ 3 * stake wl A + 2 * stake wl (L \ L') ∧
    2 * stake wr R ≤ 3 * stake wr B + 2 * stake wr (R \ R') ∧ stake wl (A ∩ B) = shared}

variable {L L' R R' : Finset ν} {wl wr : ν → ℕ}

open scoped Classical in
/-- Two quorums share at least the guaranteed intersection, under the weights of the first. -/
theorem guaranteedIntersection_le_stake_inter {A B : Finset ν} (hA : A ⊆ L)
    (quorumA : 2 * stake wl L ≤ 3 * stake wl A + 2 * stake wl (L \ L')) (hB : B ⊆ R)
    (quorumB : 2 * stake wr R ≤ 3 * stake wr B + 2 * stake wr (R \ R')) :
    guaranteedIntersection L L' R R' wl wr ≤ stake wl (A ∩ B) :=
  Nat.sInf_le ⟨A, hA, B, hB, quorumA, quorumB, rfl⟩

open scoped Classical in
/-- Some two quorums share exactly the guaranteed intersection, under the weights of the first.

So the guaranteed intersection is the least shared stake, and not only a bound on it. -/
theorem exists_stake_inter_eq_guaranteedIntersection :
    ∃ A ⊆ L, ∃ B ⊆ R, 2 * stake wl L ≤ 3 * stake wl A + 2 * stake wl (L \ L') ∧
      2 * stake wr R ≤ 3 * stake wr B + 2 * stake wr (R \ R') ∧
      stake wl (A ∩ B) = guaranteedIntersection L L' R R' wl wr := by
  -- The sets `L` and `R` are quorums of themselves, so the set of shared stakes is nonempty.
  have self (w : ν → ℕ) (S S' : Finset ν) :
      2 * stake w S ≤ 3 * stake w S + 2 * stake w (S \ S') := by
    omega
  exact Nat.sInf_mem (s := {shared | ∃ A ⊆ L, ∃ B ⊆ R,
    2 * stake wl L ≤ 3 * stake wl A + 2 * stake wl (L \ L') ∧
      2 * stake wr R ≤ 3 * stake wr B + 2 * stake wr (R \ R') ∧ stake wl (A ∩ B) = shared})
    ⟨_, L, subset_rfl, R, subset_rfl, self wl L L', self wr R R', rfl⟩

end EthLib.Consensus.Models.Ffg
