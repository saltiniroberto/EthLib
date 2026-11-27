module

public import EthLib.Consensus.Proofs.Models.Ffg.AccountableSafetyKinds
public import EthLib.Consensus.Proofs.Transition.FfgFinalityMonotonicity
public import EthLib.Consensus.Proofs.Transition.FfgVotes

/-!
# Proofs: accountable safety for two chains from one genesis state

Two chains of steps start from one genesis state, built from deposits.

When the blocks of the two finalized checkpoints conflict, validators are slashable.

The Casper FFG model bounds the stake of the slashable validators by a guaranteed intersection.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Models Models.Ffg

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

open scoped Classical in
/-- Accountable safety for two chains of steps from one genesis state.

If each step meets a stake bound and the finalized blocks conflict, slack links justify `l` and `r`.

Both lie between the finalized epochs, and some validators active at both signed two slashable data.

These validators hold at least the guaranteed intersection of the two active sets, both ways. -/
theorem accountable_safety_isSlashableAttestationData_of_chainSteps
    -- An epoch must have at least one slot, and the buffer of roots must cover three epochs.
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 3 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    -- The seed lookahead must leave room in the buffer of RANDAO mixes.
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    {fork : Fork} {state : BeaconState preset fork} {eth1BlockHash : Hash32}
    {eth1Timestamp : UInt64} {deposits : Array Deposit}
    -- The genesis state built from deposits exists only before Altair.
    (before : fork < .altair)
    (computed :
      initializeBeaconStateFromEth1 config checks eth1BlockHash eth1Timestamp deposits before =
        .ok state)
    {last₁ last₂ : ForkedBeaconState preset}
    -- Each chain ends at its last state, `last₁` or `last₂`.
    (steps₁ : Relation.ReflTransGen (ChainStep config checks) ⟨fork, state⟩ last₁)
    (steps₂ : Relation.ReflTransGen (ChainStep config checks) ⟨fork, state⟩ last₂)
    -- Each step on any run between genesis and a last state must meet the bound on the stake.
    (large₁ : ∀ forked after,
      Relation.ReflTransGen (ChainStep config checks) ⟨fork, state⟩ forked →
      ChainStep config checks forked after →
      Relation.ReflTransGen (ChainStep config checks) after last₁ →
      after.state.slot ≠ forked.state.slot →
      (forked.state.slot + 1) % preset.SLOTS_PER_EPOCH = 0 →
      3 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat <
        2 * stake (fun index => balanceAt forked.state index.toNat)
          (getActiveValidatorIndices forked.state (getCurrentEpoch forked.state)).toFinset)
    (large₂ : ∀ forked after,
      Relation.ReflTransGen (ChainStep config checks) ⟨fork, state⟩ forked →
      ChainStep config checks forked after →
      Relation.ReflTransGen (ChainStep config checks) after last₂ →
      after.state.slot ≠ forked.state.slot →
      (forked.state.slot + 1) % preset.SLOTS_PER_EPOCH = 0 →
      3 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat <
        2 * stake (fun index => balanceAt forked.state index.toNat)
          (getActiveValidatorIndices forked.state (getCurrentEpoch forked.state)).toFinset)
    -- The blocks of the two finalized checkpoints, read in the two last states, must conflict.
    --
    -- Each chain reads its finalized checkpoint in its last state.
    --
    -- The blocks of the model are the roots in the order of `ChainRoot`.
    --
    -- That order holds the links of the states of every branch from the genesis state.
    --
    -- So two blocks conflict only when no such branch links them.
    --
    -- Blocks that conflict in the ancestry of the two runs alone need not conflict in this order.
    (conflicting : Conflicting
      (toChainRoot config checks ⟨fork, state⟩ last₁.state.finalizedCheckpoint.root)
      (toChainRoot config checks ⟨fork, state⟩ last₂.state.finalizedCheckpoint.root)) :
    -- Then two checkpoints `l` and `r` of the model have the property below.
    ∃ l r : Models.Ffg.Checkpoint (ChainRoot config checks ⟨fork, state⟩),
      -- Their epochs lie between the epochs of the two finalized checkpoints.
      min last₁.state.finalizedCheckpoint.epoch.toNat
        last₂.state.finalizedCheckpoint.epoch.toNat ≤ l.epoch ∧
      l.epoch ≤ max last₁.state.finalizedCheckpoint.epoch.toNat
        last₂.state.finalizedCheckpoint.epoch.toNat ∧
      min last₁.state.finalizedCheckpoint.epoch.toNat
        last₂.state.finalizedCheckpoint.epoch.toNat ≤ r.epoch ∧
      r.epoch ≤ max last₁.state.finalizedCheckpoint.epoch.toNat
        last₂.state.finalizedCheckpoint.epoch.toNat ∧
      -- The slack links of the two chains justify them, with the votes and balances of both runs.
      JustifiedBy (fun s t => ∃ last ∈ ({last₁, last₂} : Set (ForkedBeaconState preset)),
          SlackLink (fun c => activeSetAt last.state c.epoch)
            (fun c => activeSetAt last.state (c.epoch + 1))
            (fun c => justifyingBalances config checks (toChainRoot config checks ⟨fork, state⟩)
                ⟨fork, state⟩ last₁ c ∪
              justifyingBalances config checks (toChainRoot config checks ⟨fork, state⟩)
                ⟨fork, state⟩ last₂ c)
            (ffgVotes (toChainRoot config checks ⟨fork, state⟩)
              (runVotes config checks ⟨fork, state⟩ last₁ ∪
                runVotes config checks ⟨fork, state⟩ last₂)) s t)
        (toChainRoot config checks ⟨fork, state⟩ (Vector.replicate 32 0)) l ∧
      JustifiedBy (fun s t => ∃ last ∈ ({last₁, last₂} : Set (ForkedBeaconState preset)),
          SlackLink (fun c => activeSetAt last.state c.epoch)
            (fun c => activeSetAt last.state (c.epoch + 1))
            (fun c => justifyingBalances config checks (toChainRoot config checks ⟨fork, state⟩)
                ⟨fork, state⟩ last₁ c ∪
              justifyingBalances config checks (toChainRoot config checks ⟨fork, state⟩)
                ⟨fork, state⟩ last₂ c)
            (ffgVotes (toChainRoot config checks ⟨fork, state⟩)
              (runVotes config checks ⟨fork, state⟩ last₁ ∪
                runVotes config checks ⟨fork, state⟩ last₂)) s t)
        (toChainRoot config checks ⟨fork, state⟩ (Vector.replicate 32 0)) r ∧
      -- They come with last states `a` and `b`, each one of `last₁` and `last₂`.
      ∃ a ∈ ({last₁, last₂} : Set (ForkedBeaconState preset)),
      ∃ b ∈ ({last₁, last₂} : Set (ForkedBeaconState preset)),
      -- They come with weights `wl` and `wr`, the balances of a justifying state of either run.
      ∃ wl ∈ justifyingBalances config checks (toChainRoot config checks ⟨fork, state⟩)
          ⟨fork, state⟩ last₁ l ∪
        justifyingBalances config checks (toChainRoot config checks ⟨fork, state⟩)
          ⟨fork, state⟩ last₂ l,
      ∃ wr ∈ justifyingBalances config checks (toChainRoot config checks ⟨fork, state⟩)
          ⟨fork, state⟩ last₁ r ∪
        justifyingBalances config checks (toChainRoot config checks ⟨fork, state⟩)
          ⟨fork, state⟩ last₂ r,
        -- Take `L` and `L'`, the active sets of the epoch of `l` and of the next epoch in `a`.
        --
        -- Take `R` and `R'`, the active sets of the epoch of `r` and of the next epoch in `b`.
        --
        -- Some validators of `L` and `R` each signed two attestation data.
        --
        -- The specification slashes each such pair of data.
        --
        -- Each of the two data is included in a block of one of the two runs.
        --
        -- These validators hold at least the guaranteed intersection under `wl`.
        --
        -- That is the least stake that a quorum of `L` shares with a quorum of `R`.
        --
        -- The quorum of `L` is up to the slack of `L'`, and that of `R` up to the slack of `R'`.
        guaranteedIntersection (activeSetAt a.state l.epoch) (activeSetAt a.state (l.epoch + 1))
            (activeSetAt b.state r.epoch) (activeSetAt b.state (r.epoch + 1)) wl wr ≤
          stake wl {validator ∈ activeSetAt a.state l.epoch ∩ activeSetAt b.state r.epoch |
            ∃ data1 data2,
              (validator, data1) ∈ runVotes config checks ⟨fork, state⟩ last₁ ∪
                runVotes config checks ⟨fork, state⟩ last₂ ∧
              (validator, data2) ∈ runVotes config checks ⟨fork, state⟩ last₁ ∪
                runVotes config checks ⟨fork, state⟩ last₂ ∧
              isSlashableAttestationData data1 data2 = true} ∧
        -- The second bound is the first with the two sides swapped, counted under `wr`.
        guaranteedIntersection (activeSetAt b.state r.epoch) (activeSetAt b.state (r.epoch + 1))
            (activeSetAt a.state l.epoch) (activeSetAt a.state (l.epoch + 1)) wr wl ≤
          stake wr {validator ∈ activeSetAt b.state r.epoch ∩ activeSetAt a.state l.epoch |
            ∃ data1 data2,
              (validator, data1) ∈ runVotes config checks ⟨fork, state⟩ last₁ ∪
                runVotes config checks ⟨fork, state⟩ last₂ ∧
              (validator, data2) ∈ runVotes config checks ⟨fork, state⟩ last₁ ∪
                runVotes config checks ⟨fork, state⟩ last₂ ∧
              isSlashableAttestationData data1 data2 = true} := by
  -- Each chain finalizes its checkpoint with the votes and balances of both runs.
  --
  -- The two chains read the validator set of one checkpoint from their own last states.
  --
  -- So each chain finalizes its checkpoint by slack links of its own kind, in the Casper FFG model.
  --
  -- Both chains share the votes of the two runs and the justifying balances of the two runs.
  --
  -- The model then bounds the stake of the slashable validators by a guaranteed intersection.
  --
  -- It is the least stake that two quorums share, at two justified checkpoints of the two kinds.
  obtain ⟨l, r, lo₁, hi₁, lo₂, hi₂, justifiedL, justifiedR, a, ha, b, hb, wl, hwl, wr, hwr,
      boundL, boundR⟩ :=
    accountable_safety_guaranteedIntersection (ι := ForkedBeaconState preset)
      (V := fun last c => activeSetAt last.state c.epoch)
      (U := fun last c => activeSetAt last.state (c.epoch + 1))
      (slackFinalized_activeSetAt_of_chainSteps_of_subset positive window apart computed steps₁
        (SlackStepBounds.of_toChainRoot large₁) (fun _ => Set.subset_union_left)
        Set.subset_union_left)
      (slackFinalized_activeSetAt_of_chainSteps_of_subset positive window apart computed steps₂
        (SlackStepBounds.of_toChainRoot large₂) (fun _ => Set.subset_union_right)
        Set.subset_union_right)
      conflicting
  refine ⟨l, r, lo₁, hi₁, lo₂, hi₂, justifiedL, justifiedR, a, ha, b, hb, wl, hwl, wr, hwr,
    boundL.trans (stake_mono ?_), boundR.trans (stake_mono ?_)⟩ <;>
  · -- A validator slashable in the model signed two data that the specification slashes.
    --
    -- Each slashable validator signed two attestation data that blocks of the two chains include.
    --
    -- The specification's test of an attester slashing holds for each such pair of data.
    intro validator member
    simp only [Finset.mem_filter, Finset.mem_inter] at member ⊢
    exact ⟨member.1, exists_isSlashableAttestationData_of_slashable member.2⟩

end EthLib.Consensus
