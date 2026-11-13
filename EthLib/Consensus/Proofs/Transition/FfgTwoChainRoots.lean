module

public import EthLib.Consensus.Proofs.Transition.FfgTwoChains

/-!
# Proofs: accountable safety for two chains, in the order of their own roots

Two chains of steps start from one genesis state and end at two last states.

Their roots are ordered by the links that the states on their runs record, and by no others.

Other branches from the genesis state add no link, so they add no collision of header roots.

Each step on the two runs keeps these links in order.

That is what the refinement asks of the order.

So each chain finalizes its checkpoint in this order, by slack links of its own kind.

When the blocks of the two finalized checkpoints conflict in this order, validators are slashable.

The bound on their stake is the guaranteed intersection, as for the order of `ChainRoot`.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Models Models.Ffg

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

/-- The roots, ordered by the links of the states on runs from a first state to two last states.

A state counts when a run from the first state reaches it and it reaches one of the last states. -/
def TwoChainRoot (_config : Config) (_checks : SignatureChecks)
    (_first _last₁ _last₂ : ForkedBeaconState preset) : Type :=
  Root

/-- Two roots are in order when links of states on the two runs lead from the older to the newer. -/
instance TwoChainRoot.instPreorder (first last₁ last₂ : ForkedBeaconState preset) :
    Preorder (TwoChainRoot config checks first last₁ last₂) where
  le older newer := Relation.ReflTransGen (fun older newer => ∃ forked,
    Relation.ReflTransGen (ChainStep config checks) first forked ∧
      (Relation.ReflTransGen (ChainStep config checks) forked last₁ ∨
        Relation.ReflTransGen (ChainStep config checks) forked last₂) ∧
      (older, newer) ∈ rootLinks forked.state) older newer
  le_refl _ := .refl
  le_trans _ _ _ := Relation.ReflTransGen.trans

/-- Each root as a root of the two chains from a first state. -/
def toTwoChainRoot (config : Config) (checks : SignatureChecks)
    (first last₁ last₂ : ForkedBeaconState preset) (root : Root) :
    TwoChainRoot config checks first last₁ last₂ :=
  root

/-- Each step on a run to one of the two last states meets the bounds in the order of the two runs.

The step must meet the bound on the stake. -/
theorem SlackStepBounds.of_toTwoChainRoot {first last₁ last₂ last : ForkedBeaconState preset}
    (ends : last = last₁ ∨ last = last₂)
    (large : ∀ forked after,
      Relation.ReflTransGen (ChainStep config checks) first forked →
      ChainStep config checks forked after →
      Relation.ReflTransGen (ChainStep config checks) after last →
      after.state.slot ≠ forked.state.slot →
      (forked.state.slot + 1) % preset.SLOTS_PER_EPOCH = 0 →
      3 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat <
        2 * stake (fun index => balanceAt forked.state index.toNat)
          (getActiveValidatorIndices forked.state (getCurrentEpoch forked.state)).toFinset)
    (forked after : ForkedBeaconState preset)
    (reach : Relation.ReflTransGen (ChainStep config checks) first forked)
    (step : ChainStep config checks forked after)
    (rest : Relation.ReflTransGen (ChainStep config checks) after last) :
    SlackStepBounds (toTwoChainRoot config checks first last₁ last₂) forked after := by
  refine ⟨large forked after reach step rest, fun _ member => .single ⟨after, reach.tail step, ?_,
    member⟩⟩
  rcases ends with rfl | rfl
  · exact .inl rest
  · exact .inr rest

open scoped Classical in
/-- Accountable safety for two chains of steps from one genesis state, in the order of their roots.

It is the theorem for the order of `ChainRoot`, with the order of the two runs in its place.

Each chain ends at its last state, `last₁` or `last₂`.

Each step on any run between genesis and a last state must meet the bound on the stake.

The blocks of the two finalized checkpoints must conflict in the order of the two runs.

Then two checkpoints `l` and `r` of the model have the property below.

Their epochs lie between the epochs of the two finalized checkpoints.

The slack links of the two chains justify them, with the votes and balances of both runs.

They come with last states `a` and `b`, each one of `last₁` and `last₂`.

They come with weights `wl` and `wr`, the balances of a justifying state of either run.

Take `L` and `L'`, the active sets of the epoch of `l` and of the next epoch in `a`.

Take `R` and `R'`, the active sets of the epoch of `r` and of the next epoch in `b`.

Some validators of `L` and `R` each signed two attestation data that the specification slashes.

Each of the two data is included in a block of one of the two runs.

These validators hold at least the guaranteed intersection under `wl`.

That is the least stake that a quorum of `L` up to the slack of `L'` shares with one of `R`.

The second bound is the first with the two sides swapped, counted under `wr`.

An epoch must have at least one slot, and the buffer of roots must cover three epochs.

The seed lookahead must leave room in the buffer of RANDAO mixes.

The genesis state built from deposits exists only before Altair. -/
theorem accountable_safety_isSlashableAttestationData_of_twoChainRoot
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 3 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    {fork : Fork} {state : BeaconState preset fork} {eth1BlockHash : Hash32}
    {eth1Timestamp : UInt64} {deposits : Array Deposit}
    (computed : initializeBeaconStateFromEth1 config checks eth1BlockHash eth1Timestamp deposits =
      .ok state)
    {last₁ last₂ : ForkedBeaconState preset}
    (steps₁ : Relation.ReflTransGen (ChainStep config checks) ⟨fork, state⟩ last₁)
    (steps₂ : Relation.ReflTransGen (ChainStep config checks) ⟨fork, state⟩ last₂)
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
    (conflicting : Conflicting
      (toTwoChainRoot config checks ⟨fork, state⟩ last₁ last₂
        last₁.state.finalizedCheckpoint.root)
      (toTwoChainRoot config checks ⟨fork, state⟩ last₁ last₂
        last₂.state.finalizedCheckpoint.root)) :
    ∃ l r : Models.Ffg.Checkpoint (TwoChainRoot config checks ⟨fork, state⟩ last₁ last₂),
      min last₁.state.finalizedCheckpoint.epoch.toNat
        last₂.state.finalizedCheckpoint.epoch.toNat ≤ l.epoch ∧
      l.epoch ≤ max last₁.state.finalizedCheckpoint.epoch.toNat
        last₂.state.finalizedCheckpoint.epoch.toNat ∧
      min last₁.state.finalizedCheckpoint.epoch.toNat
        last₂.state.finalizedCheckpoint.epoch.toNat ≤ r.epoch ∧
      r.epoch ≤ max last₁.state.finalizedCheckpoint.epoch.toNat
        last₂.state.finalizedCheckpoint.epoch.toNat ∧
      JustifiedBy (fun s t => ∃ last ∈ ({last₁, last₂} : Set (ForkedBeaconState preset)),
          SlackLink (fun c => activeSetAt last.state c.epoch)
            (fun c => activeSetAt last.state (c.epoch + 1))
            (fun c => justifyingBalances config checks
                (toTwoChainRoot config checks ⟨fork, state⟩ last₁ last₂) ⟨fork, state⟩ last₁ c ∪
              justifyingBalances config checks
                (toTwoChainRoot config checks ⟨fork, state⟩ last₁ last₂) ⟨fork, state⟩ last₂ c)
            (ffgVotes (toTwoChainRoot config checks ⟨fork, state⟩ last₁ last₂)
              (runVotes config checks ⟨fork, state⟩ last₁ ∪
                runVotes config checks ⟨fork, state⟩ last₂)) s t)
        (toTwoChainRoot config checks ⟨fork, state⟩ last₁ last₂ (Vector.replicate 32 0)) l ∧
      JustifiedBy (fun s t => ∃ last ∈ ({last₁, last₂} : Set (ForkedBeaconState preset)),
          SlackLink (fun c => activeSetAt last.state c.epoch)
            (fun c => activeSetAt last.state (c.epoch + 1))
            (fun c => justifyingBalances config checks
                (toTwoChainRoot config checks ⟨fork, state⟩ last₁ last₂) ⟨fork, state⟩ last₁ c ∪
              justifyingBalances config checks
                (toTwoChainRoot config checks ⟨fork, state⟩ last₁ last₂) ⟨fork, state⟩ last₂ c)
            (ffgVotes (toTwoChainRoot config checks ⟨fork, state⟩ last₁ last₂)
              (runVotes config checks ⟨fork, state⟩ last₁ ∪
                runVotes config checks ⟨fork, state⟩ last₂)) s t)
        (toTwoChainRoot config checks ⟨fork, state⟩ last₁ last₂ (Vector.replicate 32 0)) r ∧
      ∃ a ∈ ({last₁, last₂} : Set (ForkedBeaconState preset)),
      ∃ b ∈ ({last₁, last₂} : Set (ForkedBeaconState preset)),
      ∃ wl ∈ justifyingBalances config checks
          (toTwoChainRoot config checks ⟨fork, state⟩ last₁ last₂) ⟨fork, state⟩ last₁ l ∪
        justifyingBalances config checks
          (toTwoChainRoot config checks ⟨fork, state⟩ last₁ last₂) ⟨fork, state⟩ last₂ l,
      ∃ wr ∈ justifyingBalances config checks
          (toTwoChainRoot config checks ⟨fork, state⟩ last₁ last₂) ⟨fork, state⟩ last₁ r ∪
        justifyingBalances config checks
          (toTwoChainRoot config checks ⟨fork, state⟩ last₁ last₂) ⟨fork, state⟩ last₂ r,
        guaranteedIntersection (activeSetAt a.state l.epoch) (activeSetAt a.state (l.epoch + 1))
            (activeSetAt b.state r.epoch) (activeSetAt b.state (r.epoch + 1)) wl wr ≤
          stake wl {validator ∈ activeSetAt a.state l.epoch ∩ activeSetAt b.state r.epoch |
            ∃ data1 data2,
              (validator, data1) ∈ runVotes config checks ⟨fork, state⟩ last₁ ∪
                runVotes config checks ⟨fork, state⟩ last₂ ∧
              (validator, data2) ∈ runVotes config checks ⟨fork, state⟩ last₁ ∪
                runVotes config checks ⟨fork, state⟩ last₂ ∧
              isSlashableAttestationData data1 data2 = true} ∧
        guaranteedIntersection (activeSetAt b.state r.epoch) (activeSetAt b.state (r.epoch + 1))
            (activeSetAt a.state l.epoch) (activeSetAt a.state (l.epoch + 1)) wr wl ≤
          stake wr {validator ∈ activeSetAt b.state r.epoch ∩ activeSetAt a.state l.epoch |
            ∃ data1 data2,
              (validator, data1) ∈ runVotes config checks ⟨fork, state⟩ last₁ ∪
                runVotes config checks ⟨fork, state⟩ last₂ ∧
              (validator, data2) ∈ runVotes config checks ⟨fork, state⟩ last₁ ∪
                runVotes config checks ⟨fork, state⟩ last₂ ∧
              isSlashableAttestationData data1 data2 = true} := by
  -- Each chain finalizes its checkpoint in the order of the two runs.
  obtain ⟨l, r, lo₁, hi₁, lo₂, hi₂, justifiedL, justifiedR, a, ha, b, hb, wl, hwl, wr, hwr,
      boundL, boundR⟩ :=
    accountable_safety_guaranteedIntersection (ι := ForkedBeaconState preset)
      (V := fun last c => activeSetAt last.state c.epoch)
      (U := fun last c => activeSetAt last.state (c.epoch + 1))
      (slackFinalized_activeSetAt_of_chainSteps_of_subset positive window apart computed steps₁
        (SlackStepBounds.of_toTwoChainRoot (.inl rfl) large₁) (fun _ => Set.subset_union_left)
        Set.subset_union_left)
      (slackFinalized_activeSetAt_of_chainSteps_of_subset positive window apart computed steps₂
        (SlackStepBounds.of_toTwoChainRoot (.inr rfl) large₂) (fun _ => Set.subset_union_right)
        Set.subset_union_right)
      conflicting
  refine ⟨l, r, lo₁, hi₁, lo₂, hi₂, justifiedL, justifiedR, a, ha, b, hb, wl, hwl, wr, hwr,
    boundL.trans (stake_mono ?_), boundR.trans (stake_mono ?_)⟩ <;>
  · -- A validator slashable in the model signed two data that the specification slashes.
    intro validator member
    simp only [Finset.mem_filter, Finset.mem_inter] at member ⊢
    exact ⟨member.1, exists_isSlashableAttestationData_of_slashable member.2⟩

end EthLib.Consensus
