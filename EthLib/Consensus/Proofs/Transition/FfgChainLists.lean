module

public import EthLib.Consensus.Proofs.Models.Ffg.Monotonicity
public import EthLib.Consensus.Proofs.Transition.ChainList
public import EthLib.Consensus.Proofs.Transition.FfgFinalityChain

/-!
# Proofs: a chain given as its list of steps finalizes its checkpoint in Casper FFG

The theorems on runs read their votes and weights from every run between two states.

A chain given as data has its own votes and weights.

Its votes are those that the attestations of the blocks it applies cast.

Its weights are the effective balances of its own states that end an epoch.

The finalized checkpoint of its last state is slack-finalized with these votes and weights.

The validator sets are the active sets read in its last state, as for a run.

The proof is the induction of the theorem on runs, over the steps of the list.

A block step there asks only that the set of votes hold the votes of its own block.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Models Models.Ffg

variable {preset : Preset} {config : Config} {checks : SignatureChecks} {β : Type*} [Preorder β]
  {V U : Models.Ffg.Checkpoint β → Finset ValidatorIndex}
  {W : Models.Ffg.Checkpoint β → Set (ValidatorIndex → ℕ)} {genesis : β}
  {attested : Set (ValidatorIndex × AttestationData)} {block : Root → β}
  {first : ForkedBeaconState preset}

namespace ChainList

/-- The votes that the blocks a chain applies cast.

Each vote is cast by an attestation of one of these blocks.

Its committees are those of the state before the block.

So the set holds the votes that the chain includes, and no others. -/
def votes {last : ForkedBeaconState preset} (chain : ChainList config checks first last) :
    Set (ValidatorIndex × AttestationData) :=
  {vote | ∃ applied ∈ chain.appliedBlocks, vote ∈ blockVotes applied.before applied.signed.message}

/-- The effective balances of each state of a chain whose next step on it may justify a checkpoint.

That next step is a slot that ends an epoch.

The epoch of the checkpoint is the previous or the current epoch of the state.

Its block is that of the root that the state records for the start of that epoch. -/
def balances (block : Root → β) {last : ForkedBeaconState preset}
    (chain : ChainList config checks first last) (c : Models.Ffg.Checkpoint β) :
    Set (ValidatorIndex → ℕ) :=
  {weights | ∃ step ∈ chain.steps, step.2.state.slot ≠ step.1.state.slot ∧
    (step.1.state.slot + 1) % preset.SLOTS_PER_EPOCH = 0 ∧
    ∃ (current : Bool) (root : Root),
      getBlockRoot step.1.state
          (if current then getCurrentEpoch step.1.state else getPreviousEpoch step.1.state) =
        .ok root ∧
      c = ⟨block root,
        (if current then getCurrentEpoch step.1.state
          else getPreviousEpoch step.1.state).toNat⟩ ∧
      weights = fun index => balanceAt step.1.state index.toNat}

end ChainList

/-- A slot step casts no vote of a block, as a block keeps the slot and the slot step moves it. -/
theorem blockStepVotes_eq_empty_of_advanceSlotAcross {forked after : ForkedBeaconState preset}
    (computed : advanceSlotAcross config checks forked = .ok after) :
    blockStepVotes config checks forked after = ∅ := by
  ext vote
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨engine, signed, validateResult, state, rfl, applied, -⟩
  obtain ⟨-, blockOk, -⟩ := applySignedBlock_ok applied
  exact advanceSlotAcross_slot_ne computed (frame_processBlock blockOk).slot

/-- A block step keeps the properties of the states of a chain, with finality.

The set of votes must hold the votes of the block, and the block map must order the new links.

An epoch must have at least one slot, and the buffer of roots must cover three epochs.

The seed lookahead must leave room in the buffer of RANDAO mixes. -/
theorem SlackFinalityInvariant.of_applySignedBlock (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 3 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    {fork : Fork} {state after : BeaconState preset fork} {engine : ExecutionEngine preset fork}
    {signed : SignedBeaconBlock preset fork} {validateResult : Bool}
    (holds : SlackFinalityInvariant V U W genesis attested block ⟨fork, state⟩)
    (links : ∀ link ∈ rootLinks after, block link.1 ≤ block link.2)
    (included : blockVotes state signed.message ⊆ attested)
    (applied : applySignedBlock config checks engine state signed validateResult = .ok after) :
    SlackFinalityInvariant V U W genesis attested block ⟨fork, after⟩ := by
  obtain ⟨-, blockOk, -⟩ := applySignedBlock_ok applied
  have frame := frame_processBlock blockOk
  have voteFrame := voteFrame_processBlock apart blockOk
  have currentEq : getCurrentEpoch after = getCurrentEpoch state := by
    simp only [getCurrentEpoch, frame.slot]
  refine ⟨⟨frame.invariant holds.invariant, holds.early.of_frame frame,
    holds.separated.of_frame frame,
    (holds.flagsVoted.of_voteFrame voteFrame).mono (Set.union_subset subset_rfl included),
    fun before => (PendingVoted.of_processBlock before apart holds.pendingVoted blockOk).mono
      (Set.union_subset subset_rfl included) before,
    RootsAbove.of_chainStep positive (by omega) holds.roots links
      (.block engine signed validateResult applied), ?_⟩, links, ?_, ?_⟩
  · unfold SlackJustifiedCheckpoints
    rw [frame.previousJustified, frame.currentJustified]
    exact holds.slack
  · rw [currentEq]
    exact holds.bits.congr frame.slot (processBlock_blockRoots blockOk) frame.justificationBits
      frame.previousJustified frame.currentJustified
  · rw [frame.finalized]
    exact holds.finalized

namespace ChainList

/-- A chain given as data keeps the properties of its states, with finality.

Each step must meet the bounds of a step.

At a slot that ends an epoch, the sets and weights must match the state for both recent epochs.

The set of votes must hold the votes of the blocks that the chain applies.

An epoch must have at least one slot, and the buffer of roots must cover three epochs.

The seed lookahead must leave room in the buffer of RANDAO mixes. -/
theorem slackFinalityInvariant (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 3 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (holds : SlackFinalityInvariant V U W genesis attested block first) :
    ∀ {last : ForkedBeaconState preset} (chain : ChainList config checks first last),
      (∀ step ∈ chain.steps, SlackStepBounds block step.1 step.2) →
      (∀ step ∈ chain.steps, step.2.state.slot ≠ step.1.state.slot →
        (step.1.state.slot + 1) % preset.SLOTS_PER_EPOCH = 0 → ∀ current : Bool,
          TargetSetsMatch V U W block step.1.state
            (if current then getCurrentEpoch step.1.state else getPreviousEpoch step.1.state)) →
      chain.votes ⊆ attested →
      SlackFinalityInvariant V U W genesis attested block last
  | _, .nil, _, _, _ => holds
  | _, .slot earlier computed, bounds, sets, included => by
    have earlierHolds := earlier.slackFinalityInvariant positive window apart holds
      (fun step member => bounds step (List.mem_append_left _ member))
      (fun step member => sets step (List.mem_append_left _ member)) included
    have newest : _ ∈ (ChainList.slot earlier computed).steps :=
      List.mem_append_right _ (List.mem_singleton_self _)
    refine earlierHolds.of_chainStep positive window apart ⟨bounds _ newest, ?_, sets _ newest⟩
      (.slot computed)
    rw [blockStepVotes_eq_empty_of_advanceSlotAcross computed]
    exact Set.empty_subset _
  | _, .block earlier engine signed validateResult applied, bounds, sets, included => by
    have earlierHolds := earlier.slackFinalityInvariant positive window apart holds
      (fun step member => bounds step (List.mem_append_left _ member))
      (fun step member => sets step (List.mem_append_left _ member))
      (fun vote ⟨applied, member, cast⟩ => included ⟨applied, List.mem_append_left _ member, cast⟩)
    have newest : _ ∈ (ChainList.block earlier engine signed validateResult applied).steps :=
      List.mem_append_right _ (List.mem_singleton_self _)
    exact earlierHolds.of_applySignedBlock positive window apart (bounds _ newest).links
      (fun vote cast => included ⟨_, List.mem_append_right _ (List.mem_singleton_self _), cast⟩)
      applied

/-- The active sets of the last state and the balances of a chain match each step that may justify.

The step must be a step of the chain, and meet the bounds of a step. -/
theorem targetSetsMatch {last : ForkedBeaconState preset}
    (chain : ChainList config checks first last)
    {step : ForkedBeaconState preset × ForkedBeaconState preset} (member : step ∈ chain.steps)
    (bounds : SlackStepBounds block step.1 step.2)
    (moved : step.2.state.slot ≠ step.1.state.slot)
    (boundary : (step.1.state.slot + 1) % preset.SLOTS_PER_EPOCH = 0) (current : Bool) :
    TargetSetsMatch (fun c => activeSetAt last.state c.epoch)
      (fun c => activeSetAt last.state (c.epoch + 1)) (chain.balances block) block step.1.state
      (if current then getCurrentEpoch step.1.state else getPreviousEpoch step.1.state) := by
  obtain ⟨reach, chainStep, rest⟩ := chain.mem_steps member
  intro root rootOk
  obtain ⟨activeEq, -, inter⟩ :=
    (SlackStepHypotheses.of_activeSetAt reach chainStep rest bounds).sets moved boundary current
      root rootOk
  exact ⟨activeEq, ⟨step, member, moved, boundary, current, root, rootOk, rfl, rfl⟩, inter⟩

/-- Along a chain given as data from genesis, the finalized checkpoint is slack-finalized.

The validator set of a checkpoint is the active set of its epoch in the last state.

Its second set is the active set of the next epoch in the last state.

Its weights are the balances of the chain, and the votes are those its blocks cast.

Each step of the chain must meet the bounds on the stake and the blocks.

An epoch must have at least one slot, and the buffer of roots must cover three epochs.

The seed lookahead must leave room in the buffer of RANDAO mixes.

The genesis block of the model is the block of the zero root.

The genesis state built from deposits exists only before Altair. -/
theorem slackFinalized_activeSetAt (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 3 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    {fork : Fork} {state : BeaconState preset fork} {eth1BlockHash : Hash32}
    {eth1Timestamp : UInt64} {deposits : Array Deposit}
    {before : fork < .altair}
    (computed :
      initializeBeaconStateFromEth1 config checks eth1BlockHash eth1Timestamp deposits before =
        .ok state)
    {last : ForkedBeaconState preset} (chain : ChainList config checks ⟨fork, state⟩ last)
    (bounds : ∀ step ∈ chain.steps, SlackStepBounds block step.1 step.2) :
    SlackFinalized (fun c => activeSetAt last.state c.epoch)
      (fun c => activeSetAt last.state (c.epoch + 1)) (chain.balances block)
      (block (Vector.replicate 32 0)) (ffgVotes block chain.votes)
      (last.state.finalizedCheckpoint.toFfg block) :=
  (slackFinalityInvariant positive window apart
    (initializeBeaconStateFromEth1_slackFinalityInvariant computed) chain bounds
    (fun _ member moved boundary current =>
      chain.targetSetsMatch member (bounds _ member) moved boundary current)
    subset_rfl).finalized

/-- Along a chain given as data from genesis, both justified checkpoints are slack-justified.

The sets, weights and votes are those of the theorem on the finalized checkpoint.

Each step of the chain must meet the bounds on the stake and the blocks.

An epoch must have at least one slot, and the buffer of roots must cover three epochs.

The seed lookahead must leave room in the buffer of RANDAO mixes.

The genesis block of the model is the block of the zero root. -/
theorem slackJustifiedCheckpoints_activeSetAt (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 3 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    {fork : Fork} {state : BeaconState preset fork} {eth1BlockHash : Hash32}
    {eth1Timestamp : UInt64} {deposits : Array Deposit}
    {before : fork < .altair}
    (computed :
      initializeBeaconStateFromEth1 config checks eth1BlockHash eth1Timestamp deposits before =
        .ok state)
    {last : ForkedBeaconState preset} (chain : ChainList config checks ⟨fork, state⟩ last)
    (bounds : ∀ step ∈ chain.steps, SlackStepBounds block step.1 step.2) :
    SlackJustifiedCheckpoints (fun c => activeSetAt last.state c.epoch)
      (fun c => activeSetAt last.state (c.epoch + 1)) (chain.balances block)
      (block (Vector.replicate 32 0)) (ffgVotes block chain.votes) block last.state :=
  (slackFinalityInvariant positive window apart
    (initializeBeaconStateFromEth1_slackFinalityInvariant computed) chain bounds
    (fun _ member moved boundary current =>
      chain.targetSetsMatch member (bounds _ member) moved boundary current)
    subset_rfl).slack

/-- A chain's finalized checkpoint remains slack-finalized with more votes and allowed weights.

The validator sets are the active sets read in the last state, as in the theorem on chains.

The larger sets must contain the votes and the balances of the chain. -/
theorem slackFinalized_activeSetAt_of_subset (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 3 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    {fork : Fork} {state : BeaconState preset fork} {eth1BlockHash : Hash32}
    {eth1Timestamp : UInt64} {deposits : Array Deposit}
    {before : fork < .altair}
    (computed :
      initializeBeaconStateFromEth1 config checks eth1BlockHash eth1Timestamp deposits before =
        .ok state)
    {last : ForkedBeaconState preset} (chain : ChainList config checks ⟨fork, state⟩ last)
    (bounds : ∀ step ∈ chain.steps, SlackStepBounds block step.1 step.2)
    (weights : ∀ c, chain.balances block c ⊆ W c) (included : chain.votes ⊆ attested) :
    SlackFinalized (fun c => activeSetAt last.state c.epoch)
      (fun c => activeSetAt last.state (c.epoch + 1)) W (block (Vector.replicate 32 0))
      (ffgVotes block attested) (last.state.finalizedCheckpoint.toFfg block) :=
  SlackFinalized.mono (slackFinalized_activeSetAt positive window apart computed chain bounds)
    weights (Set.image_mono included)

end ChainList

end EthLib.Consensus
