module

public import EthLib.Consensus.Proofs.Models.Ffg.AccountableSafety
public import EthLib.Consensus.Proofs.Models.Ffg.GuaranteedIntersection

/-!
# Casper FFG: accountable safety with slack links of several kinds

Two chains can read the validator set of one checkpoint from two different states.

So each chain gives its own validator sets and second sets to the slack links that it finalizes by.

Each kind `i` of slack link has the validator sets `V i` and the second sets `U i`.

All kinds share the set of votes and the sets of allowed weights.

The proof of Gasper Lemma 8.2 uses only the order of each link, so it holds for links of any kind.

It finds two links whose double voters are slashable.

The voters of each link are a quorum up to slack of the validator set of its own kind.

So the slashable validators hold at least the guaranteed intersection of the two quorums.

The bound needs no arithmetic on the sets, and it loses no stake to a change of the sets.

The paper is [arXiv 2003.03052v3](https://arxiv.org/abs/2003.03052v3).
-/

@[expose] public section

namespace EthLib.Consensus.Models.Ffg

variable {ν β ι : Type*} [Preorder β] {V U : ι → Checkpoint β → Finset ν}
  {W : Checkpoint β → Set (ν → ℕ)} {genesis : β} {votes : Set (Vote ν β)}

open scoped Classical in
/-- Accountable safety with slack links of two kinds, bounded by a guaranteed intersection.

Take two checkpoints whose blocks conflict.

The first is slack-finalized by the links of kind `i₁`, and the second by those of kind `i₂`.

Then two checkpoints `l` and `r` have the property below.

Their epochs lie between the epochs of the two finalized checkpoints.

Slack links of the two kinds justify them.

They come with kinds `i` and `j` among `i₁` and `i₂`, and with weights `wl` and `wr`.

The weights `wl` are allowed at `l`, and `wr` at `r`.

Take `L` and `L'`, the validator set and the second set of kind `i` at `l`.

Take `R` and `R'`, the validator set and the second set of kind `j` at `r`.

The slashable validators of `L` and `R` hold at least the guaranteed intersection under `wl`.

That is the least stake that a quorum of `L` up to the slack of `L'` shares with one of `R`.

The quorum of `L` is counted under `wl`, and that of `R` under `wr`.

The second bound is the first with the two sides swapped, counted under `wr`.

With one kind, the bounds hold for the slack links of `accountable_safety_dynamic_slack`. -/
theorem accountable_safety_guaranteedIntersection {i₁ i₂ : ι} {c₁ c₂ : Checkpoint β}
    (h₁ : SlackFinalized (V i₁) (U i₁) W genesis votes c₁)
    (h₂ : SlackFinalized (V i₂) (U i₂) W genesis votes c₂)
    (hc : Conflicting c₁.block c₂.block) :
    ∃ l r : Checkpoint β, min c₁.epoch c₂.epoch ≤ l.epoch ∧ l.epoch ≤ max c₁.epoch c₂.epoch ∧
      min c₁.epoch c₂.epoch ≤ r.epoch ∧ r.epoch ≤ max c₁.epoch c₂.epoch ∧
      JustifiedBy (fun s t => ∃ i ∈ ({i₁, i₂} : Set ι), SlackLink (V i) (U i) W votes s t)
        genesis l ∧
      JustifiedBy (fun s t => ∃ i ∈ ({i₁, i₂} : Set ι), SlackLink (V i) (U i) W votes s t)
        genesis r ∧
      ∃ i ∈ ({i₁, i₂} : Set ι), ∃ j ∈ ({i₁, i₂} : Set ι), ∃ wl ∈ W l, ∃ wr ∈ W r,
        guaranteedIntersection (V i l) (U i l) (V j r) (U j r) wl wr ≤
          stake wl {v ∈ V i l ∩ V j r | Slashable votes v} ∧
        guaranteedIntersection (V j r) (U j r) (V i l) (U i l) wr wl ≤
          stake wr {v ∈ V j r ∩ V i l | Slashable votes v} := by
  -- Both finalizations hold for the links of either kind, which go forward like each kind.
  obtain ⟨s₁, t₁, s₂, t₂, lo₁, hi₁, lo₂, hi₂, hs₁, hs₂, hl₁, hl₂, h⟩ :=
    (h₁.imp (link' := fun s t => ∃ i ∈ ({i₁, i₂} : Set ι), SlackLink (V i) (U i) W votes s t)
      fun linked => ⟨i₁, by simp, linked⟩).slashableLinksBy (ν := ν)
      (fun ⟨_, _, linked⟩ => linked.ordered) (h₂.imp fun linked => ⟨i₂, by simp, linked⟩) hc
  -- Each link has its kind, and its voters are a quorum up to slack under its weights.
  obtain ⟨i, hi, -, -, wl, hwl, quorumL⟩ := id hl₁
  obtain ⟨j, hj, -, -, wr, hwr, quorumR⟩ := id hl₂
  refine ⟨t₁, t₂, lo₁, hi₁, lo₂, hi₂, .link hs₁ hl₁, .link hs₂ hl₂, i, hi, j, hj, wl, hwl, wr, hwr,
    (guaranteedIntersection_le_stake_inter (Finset.filter_subset _ _) quorumL
      (Finset.filter_subset _ _) quorumR).trans (stake_mono ?_),
    (guaranteedIntersection_le_stake_inter (Finset.filter_subset _ _) quorumR
      (Finset.filter_subset _ _) quorumL).trans (stake_mono ?_)⟩ <;>
  · -- A validator that votes for both links signs the two votes that break a condition.
    intro v member
    simp only [Finset.mem_inter, Finset.mem_filter] at member ⊢
    first
      | exact ⟨⟨member.1.1, member.2.1⟩, _, member.1.2, _, member.2.2, rfl, rfl, h v⟩
      | exact ⟨⟨member.1.1, member.2.1⟩, _, member.2.2, _, member.1.2, rfl, rfl, h v⟩

end EthLib.Consensus.Models.Ffg
