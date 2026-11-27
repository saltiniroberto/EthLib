module

public import EthLib.Consensus.Proofs.Models.Ffg.AccountableSafetyKinds
public import EthLib.Consensus.Proofs.Transition.FfgChainLists
public import EthLib.Consensus.Proofs.Transition.FfgVotes

/-!
# Proofs: accountable safety for two chains given as lists, in the order of their roots

Two chains given as data start from one genesis state and end at two last states.

Their roots are ordered by the links that the states of the two lists record, and by no others.

When the blocks of the two finalized checkpoints conflict in this order, validators are slashable.

The bound on their stake is the guaranteed intersection, as for the order of `ChainRoot`.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Models Models.Ffg

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

/-- The roots, ordered by the links that the states of a list record. -/
def StatesRoot (_states : List (ForkedBeaconState preset)) : Type :=
  Root

/-- Two roots are in order when links of states of the list lead from the older to the newer. -/
instance StatesRoot.instPreorder (states : List (ForkedBeaconState preset)) :
    Preorder (StatesRoot states) where
  le older newer := Relation.ReflTransGen (fun older newer => ∃ forked ∈ states,
    (older, newer) ∈ rootLinks forked.state) older newer
  le_refl _ := .refl
  le_trans _ _ _ := Relation.ReflTransGen.trans

/-- Each root as a root ordered by the links of a list of states. -/
def toStatesRoot (states : List (ForkedBeaconState preset)) (root : Root) : StatesRoot states :=
  root

/-- Each step of a chain meets the bounds of a step, in the order of a list that holds its states.

The step must meet the bound on the stake. -/
theorem ChainList.slackStepBounds_toStatesRoot {first last : ForkedBeaconState preset}
    (chain : ChainList config checks first last) {states : List (ForkedBeaconState preset)}
    (included : ∀ forked ∈ chain.states, forked ∈ states)
    (large : ∀ step ∈ chain.steps, step.2.state.slot ≠ step.1.state.slot →
      (step.1.state.slot + 1) % preset.SLOTS_PER_EPOCH = 0 →
      3 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat <
        2 * stake (fun index => balanceAt step.1.state index.toNat)
          (getActiveValidatorIndices step.1.state (getCurrentEpoch step.1.state)).toFinset)
    {step : ForkedBeaconState preset × ForkedBeaconState preset} (member : step ∈ chain.steps) :
    SlackStepBounds (toStatesRoot states) step.1 step.2 :=
  -- Each step of the two lists keeps in order the links that its states record.
  --
  -- That is what the refinement asks.
  ⟨large step member, fun _ link =>
    .single ⟨step.2, included _ (chain.snd_mem_states member), link⟩⟩

open scoped Classical in
/-- Accountable safety for two chains given as lists from one genesis state, in their root order.

If each step meets a stake bound and the finalized blocks conflict, slack links justify `l` and `r`.

Both lie between the finalized epochs, and some validators active at both signed two slashable data.

These validators hold at least the guaranteed intersection of the two active sets, both ways. -/
theorem accountable_safety_isSlashableAttestationData_of_statesRoot
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
    -- Each list ends at its last state, `last₁` or `last₂`.
    (chain₁ : ChainList config checks ⟨fork, state⟩ last₁)
    (chain₂ : ChainList config checks ⟨fork, state⟩ last₂)
    -- Each step of each list must meet the bound on the stake.
    (large₁ : ∀ step ∈ chain₁.steps, step.2.state.slot ≠ step.1.state.slot →
      (step.1.state.slot + 1) % preset.SLOTS_PER_EPOCH = 0 →
      3 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat <
        2 * stake (fun index => balanceAt step.1.state index.toNat)
          (getActiveValidatorIndices step.1.state (getCurrentEpoch step.1.state)).toFinset)
    (large₂ : ∀ step ∈ chain₂.steps, step.2.state.slot ≠ step.1.state.slot →
      (step.1.state.slot + 1) % preset.SLOTS_PER_EPOCH = 0 →
      3 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat <
        2 * stake (fun index => balanceAt step.1.state index.toNat)
          (getActiveValidatorIndices step.1.state (getCurrentEpoch step.1.state)).toFinset)
    -- The roots are ordered by the links that the states of the two lists record.
    --
    -- The blocks of the two finalized checkpoints must conflict in that order.
    (conflicting : Conflicting
      (toStatesRoot (chain₁.states ++ chain₂.states) last₁.state.finalizedCheckpoint.root)
      (toStatesRoot (chain₁.states ++ chain₂.states) last₂.state.finalizedCheckpoint.root)) :
    -- Then two checkpoints `l` and `r` of the model have the property below.
    ∃ l r : Models.Ffg.Checkpoint (StatesRoot (chain₁.states ++ chain₂.states)),
      -- Their epochs lie between the epochs of the two finalized checkpoints.
      min last₁.state.finalizedCheckpoint.epoch.toNat
        last₂.state.finalizedCheckpoint.epoch.toNat ≤ l.epoch ∧
      l.epoch ≤ max last₁.state.finalizedCheckpoint.epoch.toNat
        last₂.state.finalizedCheckpoint.epoch.toNat ∧
      min last₁.state.finalizedCheckpoint.epoch.toNat
        last₂.state.finalizedCheckpoint.epoch.toNat ≤ r.epoch ∧
      r.epoch ≤ max last₁.state.finalizedCheckpoint.epoch.toNat
        last₂.state.finalizedCheckpoint.epoch.toNat ∧
      -- The slack links of the two chains justify them, with the votes and balances of both lists.
      JustifiedBy (fun s t => ∃ last ∈ ({last₁, last₂} : Set (ForkedBeaconState preset)),
          SlackLink (fun c => activeSetAt last.state c.epoch)
            (fun c => activeSetAt last.state (c.epoch + 1))
            (fun c => chain₁.balances (toStatesRoot (chain₁.states ++ chain₂.states)) c ∪
              chain₂.balances (toStatesRoot (chain₁.states ++ chain₂.states)) c)
            (ffgVotes (toStatesRoot (chain₁.states ++ chain₂.states))
              (chain₁.votes ∪ chain₂.votes)) s t)
        (toStatesRoot (chain₁.states ++ chain₂.states) (Vector.replicate 32 0)) l ∧
      JustifiedBy (fun s t => ∃ last ∈ ({last₁, last₂} : Set (ForkedBeaconState preset)),
          SlackLink (fun c => activeSetAt last.state c.epoch)
            (fun c => activeSetAt last.state (c.epoch + 1))
            (fun c => chain₁.balances (toStatesRoot (chain₁.states ++ chain₂.states)) c ∪
              chain₂.balances (toStatesRoot (chain₁.states ++ chain₂.states)) c)
            (ffgVotes (toStatesRoot (chain₁.states ++ chain₂.states))
              (chain₁.votes ∪ chain₂.votes)) s t)
        (toStatesRoot (chain₁.states ++ chain₂.states) (Vector.replicate 32 0)) r ∧
      -- They come with last states `a` and `b`, each one of `last₁` and `last₂`.
      ∃ a ∈ ({last₁, last₂} : Set (ForkedBeaconState preset)),
      ∃ b ∈ ({last₁, last₂} : Set (ForkedBeaconState preset)),
      -- They come with weights `wl` and `wr`, the balances of a state of either list.
      ∃ wl ∈ chain₁.balances (toStatesRoot (chain₁.states ++ chain₂.states)) l ∪
        chain₂.balances (toStatesRoot (chain₁.states ++ chain₂.states)) l,
      ∃ wr ∈ chain₁.balances (toStatesRoot (chain₁.states ++ chain₂.states)) r ∪
        chain₂.balances (toStatesRoot (chain₁.states ++ chain₂.states)) r,
        -- Take `L` and `L'`, the active sets of the epoch of `l` and of the next epoch in `a`.
        --
        -- Take `R` and `R'`, the active sets of the epoch of `r` and of the next epoch in `b`.
        --
        -- Some validators of `L` and `R` each signed two attestation data.
        --
        -- The specification slashes each such pair of data.
        --
        -- Each of the two data is included in a block that one of the two lists applies.
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
              (validator, data1) ∈ chain₁.votes ∪ chain₂.votes ∧
              (validator, data2) ∈ chain₁.votes ∪ chain₂.votes ∧
              isSlashableAttestationData data1 data2 = true} ∧
        -- The second bound is the first with the two sides swapped, counted under `wr`.
        guaranteedIntersection (activeSetAt b.state r.epoch) (activeSetAt b.state (r.epoch + 1))
            (activeSetAt a.state l.epoch) (activeSetAt a.state (l.epoch + 1)) wr wl ≤
          stake wr {validator ∈ activeSetAt b.state r.epoch ∩ activeSetAt a.state l.epoch |
            ∃ data1 data2,
              (validator, data1) ∈ chain₁.votes ∪ chain₂.votes ∧
              (validator, data2) ∈ chain₁.votes ∪ chain₂.votes ∧
              isSlashableAttestationData data1 data2 = true} := by
  -- Each list finalizes its checkpoint in the order of the two lists, with its own votes.
  --
  -- So each chain finalizes its checkpoint in this order, with its own votes and balances.
  obtain ⟨l, r, lo₁, hi₁, lo₂, hi₂, justifiedL, justifiedR, a, ha, b, hb, wl, hwl, wr, hwr,
      boundL, boundR⟩ :=
    accountable_safety_guaranteedIntersection (ι := ForkedBeaconState preset)
      (V := fun last c => activeSetAt last.state c.epoch)
      (U := fun last c => activeSetAt last.state (c.epoch + 1))
      (chain₁.slackFinalized_activeSetAt_of_subset positive window apart computed
        (fun _ member => chain₁.slackStepBounds_toStatesRoot
          (fun _ held => List.mem_append_left _ held) large₁ member)
        (fun _ => Set.subset_union_left) Set.subset_union_left)
      (chain₂.slackFinalized_activeSetAt_of_subset positive window apart computed
        (fun _ member => chain₂.slackStepBounds_toStatesRoot
          (fun _ held => List.mem_append_right _ held) large₂ member)
        (fun _ => Set.subset_union_right) Set.subset_union_right)
      conflicting
  refine ⟨l, r, lo₁, hi₁, lo₂, hi₂, justifiedL, justifiedR, a, ha, b, hb, wl, hwl, wr, hwr,
    boundL.trans (stake_mono ?_), boundR.trans (stake_mono ?_)⟩ <;>
  · -- A validator slashable in the model signed two data that the specification slashes.
    --
    -- Each of the two data is included in a block that one of the two lists applies.
    intro validator member
    simp only [Finset.mem_filter, Finset.mem_inter] at member ⊢
    exact ⟨member.1, exists_isSlashableAttestationData_of_slashable member.2⟩

end EthLib.Consensus
